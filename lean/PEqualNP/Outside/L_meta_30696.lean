import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30696_aux
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
def goal_255 : Nat := 0xfffffffefffffffefffffffefffffffcfffffffefffffffaffeeffeeeeeeaa00
def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_251 : Nat := 0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0f0c0f0f0f0e0f0f0f0a0f0e0f0e0e0e0a00
def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_187 : Nat := 0xf0f0f0e0f0f0f0c00000000000000000f0e0f0e0e0e0a00
def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_186 : Nat := 0x50505040505050400000000000000000504050404040000
def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_178 : Nat := 0x500040005000400000000000000000004000400040000
def dom_146 : Nat := 0x5000500000000000000000000000000050005
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_146 : Nat := 0x5000400000000000000000000000000040000
def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_185 : Nat := 0x30303020303030000000000000000000302030202020200
def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_169 : Nat := 0x3020000030000000000000000000000030200000200
def dom_41 : Nat := 0x30300000303
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_41 : Nat := 0x30200000200
def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_179 : Nat := 0xf000e000f000c0000000000000000000e000e000e0000
def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_171 : Nat := 0xf0e00000f0c000000000000000000000f0e00000a00
def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_155 : Nat := 0xf0f0f0c0000000000000000000000000e0e0a00
def dom_154 : Nat := 0x505050500000000000000000000000005050505
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_154 : Nat := 0x505050400000000000000000000000004040000
def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_59 : Nat := 0xf0e0f0e0e0e0a00
def dom_57 : Nat := 0x303030303030303
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_57 : Nat := 0x302030202020200
def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_147 : Nat := 0xf000c000000000000000000000000000e0000
def dom_43 : Nat := 0xf0f00000f0f
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_43 : Nat := 0xf0e00000a00
def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_184 : Nat := 0x10101000101010000000000000000000100010000000000
def dom_58 : Nat := 0x505050505050505
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_58 : Nat := 0x504050404040000
def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_177 : Nat := 0x300020003000000000000000000000002000200020000
def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_163 : Nat := 0xe0000000c00000000000000000000000e00000000
def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_139 : Nat := 0xf0c00000000000000000000000000000a00
def dom_27 : Nat := 0xf0f0f0f
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]
def goal_27 : Nat := 0xe0e0a00
def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_123 : Nat := 0xf0f0f0e0f0f0f0a0f0e0f0e0e0e0a00
def dom_122 : Nat := 0x5050505050505050505050505050505
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_122 : Nat := 0x5050504050505000504050404040000
def dom_120 : Nat := 0x1010101010101010101010101010101
def roots_120 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_120 : Nat := 0x1010100010101000100010000000000
def dom_114 : Nat := 0x50005000500050005000500050005
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_114 : Nat := 0x50004000500000004000400040000
def dom_106 : Nat := 0x505000005050000050500000505
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_106 : Nat := 0x504000005000000050400000000
def dom_90 : Nat := 0x50505050000000005050505
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_90 : Nat := 0x50505000000000004040000
def dom_121 : Nat := 0x3030303030303030303030303030303
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_121 : Nat := 0x3030302030303020302030202020200
def dom_113 : Nat := 0x30003000300030003000300030003
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_113 : Nat := 0x30002000300020002000200020000
def dom_81 : Nat := 0x300030000000000030003
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_81 : Nat := 0x300020000000000020000
def dom_105 : Nat := 0x303000003030000030300000303
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_105 : Nat := 0x302000003020000030200000200
def dom_73 : Nat := 0x3030000000000000303
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]
def goal_73 : Nat := 0x3020000000000000200
def dom_89 : Nat := 0x30303030000000003030303
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_89 : Nat := 0x30303020000000002020200
def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_107 : Nat := 0xf0e00000f0a00000f0e00000a00
def goal_105_l32 : Nat := 0x303000003020000030300000200
def dzo_105_2 : Nat := 0xc0c00000c0c00000c0c00000c0c
def gzo_105_2_32 : Nat := 0xc0c00000c0800000c0c00000800
def dom_99 : Nat := 0xf0000000f0000000f0000000f
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_99 : Nat := 0xe0000000a0000000e00000000
def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_91 : Nat := 0xf0f0f0a000000000e0e0a00
def goal_89_l16 : Nat := 0x30303020000000003030200
def dzo_89_2 : Nat := 0xc0c0c0c000000000c0c0c0c
def gzo_89_2_16 : Nat := 0xc0c0c08000000000c0c0800
def dom_83 : Nat := 0xf000f00000000000f000f
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_83 : Nat := 0xf000a00000000000e0000
def goal_121_l48 : Nat := 0x3030303030303020303030303030200
def dzo_121_2 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_121_2_48 : Nat := 0xc0c0c0c0c0c0c080c0c0c0c0c0c0800
def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_115 : Nat := 0xf000e000f000a000e000e000e0000
def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_250 : Nat := 0x505050405050504050505040505050405050504050505000504050404040000
def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_242 : Nat := 0x5000400050004000500040005000400050004000500000004000400040000
def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_210 : Nat := 0x50004000000000005000400000000000500000000000000040000
def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_218 : Nat := 0x5050504000000000505050400000000050505000000000004040000
def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_248 : Nat := 0x101010001010100010101000101010001010100010101000100010000000000
def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_234 : Nat := 0x50400000504000005040000050400000504000005000000050400000000
def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_202 : Nat := 0x504000000000000050400000000000005000000000000000000
def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_243 : Nat := 0xf000e000f000e000f000e000f000c000f000e000f000a000e000e000e0000
def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_211 : Nat := 0xf000e00000000000f000c00000000000f000a00000000000e0000
def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_209 : Nat := 0x30002000000000003000000000000000300020000000000020000
def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_235 : Nat := 0xf0e00000f0e00000f0e00000f0c00000f0e00000f0a00000f0e00000a00
def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_203 : Nat := 0xf0e0000000000000f0c0000000000000f0a0000000000000a00
def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_201 : Nat := 0x302000000000000030000000000000003020000000000000200
def goal_201_l128 : Nat := 0x303000000000000030300000000000003020000000000000200
def dzo_201_2 : Nat := 0xc0c0000000000000c0c0000000000000c0c0000000000000c0c
def gzo_201_2_128 : Nat := 0xc0c0000000000000c0c0000000000000c080000000000000800
def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_233 : Nat := 0x30200000302000003020000030000000302000003020000030200000200
def goal_233_l160 : Nat := 0x30300000303000003030000030300000303000003020000030300000200
def dzo_233_2 : Nat := 0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2_160 : Nat := 0xc0c00000c0c00000c0c00000c0c00000c0c00000c0800000c0c00000800
def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_227 : Nat := 0xe0000000e0000000e0000000c0000000e0000000a0000000e00000000
def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_219 : Nat := 0xf0f0f0e000000000f0f0f0c000000000f0f0f0a000000000e0e0a00
def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_249 : Nat := 0x303030203030302030303020303030003030302030303020302030202020200
def goal_249_l176 : Nat := 0x303030303030303030303030303030303030303030303020303030303030200
def dzo_249_2 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2_176 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0800
def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_241 : Nat := 0x3000200030002000300020003000000030002000300020002000200020000
def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_217 : Nat := 0x3030302000000000303030000000000030303020000000002020200

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
    [(0x500050000000000000000000000000005000500000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_146

theorem low_186 : Lower true dom_186 roots_186 goal_186 6 :=
  lower_slice (d:=dom_186) (dSub:=dom_178) (T:=goal_186) (TSub:=goal_178) (roots:=roots_186) (rootsSub:=roots_178)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000500050000000000000000000500050005000500, 32, 40)] (by decide +kernel) (by decide +kernel) low_178

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

theorem low_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_slice (d:=dom_169) (dSub:=dom_41) (T:=goal_169) (TSub:=goal_41) (roots:=roots_169) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030000030300000000000000000000000000000000, 8, 136)] (by decide +kernel) (by decide +kernel) low_41

theorem low_185 : Lower true dom_185 roots_185 goal_185 6 :=
  lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185) (TSub:=goal_169) (roots:=roots_185) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000303000000000000000000000303000003030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_169

theorem low_179 : Lower true dom_179 roots_179 goal_179 6 :=
  lower_slice (d:=dom_179) (dSub:=dom_178) (T:=goal_179) (TSub:=goal_178) (roots:=roots_179) (rootsSub:=roots_178)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a0000000000000000000a000a000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_178

theorem low_171 : Lower true dom_171 roots_171 goal_171 6 :=
  lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171) (TSub:=goal_169) (roots:=roots_171) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c000000000000000000000c0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) low_169

theorem low_154 : Lower true dom_154 roots_154 goal_154 5 :=
  lower_slice (d:=dom_154) (dSub:=dom_146) (T:=goal_154) (TSub:=goal_146) (roots:=roots_154) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050000000000000000000000000005000500, 128, 136)] (by decide +kernel) (by decide +kernel) low_146

theorem low_155 : Lower true dom_155 roots_155 goal_155 6 :=
  lower_slice (d:=dom_155) (dSub:=dom_154) (T:=goal_155) (TSub:=goal_154) (roots:=roots_155) (rootsSub:=roots_154)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0000000000000000000000000a0a0a0a, 8, 9)] (by decide +kernel) (by decide +kernel) low_154

theorem low_57 : Lower true dom_57 roots_57 goal_57 5 :=
  lower_slice (d:=dom_57) (dSub:=dom_41) (T:=goal_57) (TSub:=goal_41) (roots:=roots_57) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_41

theorem low_59 : Lower true dom_59 roots_59 goal_59 6 :=
  lower_slice (d:=dom_59) (dSub:=dom_57) (T:=goal_59) (TSub:=goal_57) (roots:=roots_59) (rootsSub:=roots_57)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) low_57

theorem low_147 : Lower true dom_147 roots_147 goal_147 5 :=
  lower_slice (d:=dom_147) (dSub:=dom_146) (T:=goal_147) (TSub:=goal_146) (roots:=roots_147) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000000000000000000000000000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_146

theorem low_43 : Lower true dom_43 roots_43 goal_43 5 :=
  lower_slice (d:=dom_43) (dSub:=dom_41) (T:=goal_43) (TSub:=goal_41) (roots:=roots_43) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) low_41

namespace S_184
def pairsG : List (Nat × Nat) := [(8,40), (8,136), (16,144), (24,56), (24,152), (32,40), (48,56), (48,176), (128,136), (128,144), (160,168), (160,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_184.map (· &&& dom_184)
def goalM : Nat := goal_184 &&& dom_184
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xab2d6
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x80808080808080800000000000000000000000000000004040404000000000000000000000000040404040000000202000002020000000000000000000002020000020200010001000100010000000000000000000100010001000100
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 185 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_184 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_184 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_184 == dom_184) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_184 goalM v ys) : RunD true dom_184 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_184 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_184 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_184 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_184 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_184 roots_184 goal_184 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_184

theorem low_184 : Lower true dom_184 roots_184 goal_184 4 := S_184.noCircuit

namespace S_58
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (8,40), (10,26), (10,42), (16,18), (24,26), (24,56), (32,34), (32,40), (48,50), (48,56)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_58.map (· &&& dom_58)
def goalM : Nat := goal_58 &&& dom_58
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xd553f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a0a0a0000000141400001414000280028002800280404040404040404
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 59 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_58 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_58 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_58 == dom_58) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_58 goalM v ys) : RunD true dom_58 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_58 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_58 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_58 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_58 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_58 roots_58 goal_58 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_58

theorem low_58 : Lower true dom_58 roots_58 goal_58 4 := S_58.noCircuit

namespace S_177
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (16,17), (16,144), (32,33), (48,49), (48,176), (128,144), (129,145), (129,161), (160,161), (160,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_177.map (· &&& dom_177)
def goalM : Nat := goal_177 &&& dom_177
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x9e687
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xc000c000c000c0000000000000000000000000000000300030000000000000000000000000003000300000000c0000000c00000000000000000000000c0000000c000200020002000200000000000000000002000200020002
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 178 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_177 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_177 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xffffffff00000000ffffffff00000000, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_177 == dom_177) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_177 goalM v ys) : RunD true dom_177 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_177 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_177 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_177 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_177 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_177 roots_177 goal_177 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_177

theorem low_177 : Lower true dom_177 roots_177 goal_177 4 := S_177.noCircuit

namespace S_163
def pairsG : List (Nat × Nat) := [(1,33), (2,34), (2,130), (3,35), (3,131), (32,33), (32,34), (128,130), (129,131), (129,161), (160,161), (160,162)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_163.map (· &&& dom_163)
def goalM : Nat := goal_163 &&& dom_163
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x8cf3b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0000000f00000000000000000000000000000000f0000000000000000000000000000000f00000000c0000000c00000000000000000000000c0000000ca0000000a00000000000000000000000a0000000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 164 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_163 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_163 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_163 == dom_163) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_163 goalM v ys) : RunD true dom_163 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_163 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_163 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_163 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_163 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_163 roots_163 goal_163 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_163

theorem low_163 : Lower true dom_163 roots_163 goal_163 4 := S_163.noCircuit

namespace S_139
def pairsG : List (Nat × Nat) := [(1,9), (2,130), (3,11), (3,131), (8,9), (8,136), (10,11), (10,138), (128,130), (128,136), (129,131), (129,137)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_139.map (· &&& dom_139)
def goalM : Nat := goal_139 &&& dom_139
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xa2b9f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f00000000000000000000000000000000f0000000000000000000000000000000f00c0c00000000000000000000000000000c0ca0a00000000000000000000000000000a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 140 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_139 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_139 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_139 == dom_139) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_139 goalM v ys) : RunD true dom_139 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_139 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_139 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_139 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_139 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_139 roots_139 goal_139 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_139

theorem low_139 : Lower true dom_139 roots_139 goal_139 4 := S_139.noCircuit

namespace S_27
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (2,18), (3,11), (3,19), (8,9), (10,11), (10,26), (16,17), (16,18), (24,25), (24,26)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x77db1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0000f000f00c0c0c0ca0a0a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 28 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_27 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_27 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_27 goalM v ys) : RunD true dom_27 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_27 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_27 roots_27 goal_27 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_27

theorem low_27 : Lower true dom_27 roots_27 goal_27 4 := S_27.noCircuit

namespace S_187
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (2,18), (2,34), (2,130), (3,11), (3,19), (3,35), (3,131), (8,9), (8,40), (8,136), (10,11), (10,26), (10,42), (10,138), (16,17), (16,18), (16,144), (24,25), (24,26), (24,56), (24,152), (32,33), (32,34), (32,40), (48,49), (48,50), (48,56), (48,176), (128,130), (128,136), (128,144), (129,131), (129,137), (129,145), (129,161), (160,161), (160,162), (160,168), (160,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_187.map (· &&& dom_187)
def goalM : Nat := goal_187 &&& dom_187
def NN : Nat → Nat
|4=>0x9
|5=>0x29
|6=>0x8b
|7=>0x49
|8=>0xa
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x4d68b485c247b2842d162fbe6197310884b05491050fc
|5,0=>0x8503b5e132521e74b94d4886d42c163dfc13d0a439db433b833229831d8029aff261b12556b21ebf2128f1fc801ea0e1a5981893416dfe168db164e71544911bab119ff118031046f0f6db0edb10c6970b94e09de108da508c9f06edd06d0904374036b901250
|6,0=>0x44b9a4434840b013b6853b0ff3a4803965b38e713877b3758d36ed03538a307402f5562e52d2e4b72e24f2da2529e8f28f2028e12267b5266722551f2506424e6d24dc523ebe23d352384c2220220d12209f72087a1f9691f67d1f4981f1601edbc1ec6b1c3711bd641b4ce1b0251983018e34181901787916bd91625015f6515dad15606153bf14fdd14f0614dcb13adb13a3c135d111d6a10e9710a6d100360fff00fb300f5150f1860f0210f0030e7b10e74a0db410da960d8b00d2630d1350c8840c52f0bb100b9960b9330a8510a2ba09e5b0930b08d4f08c9f0883b0816e07a570795e077e306f8806da606cde069a9068670676b0661c0609405b8b05a120583a057d804e4504db904b3c04a4b049df047b60414903e7103dab038d90351202b6b02ab202863026d60227d021c4020ad0207801be5019840125000924
|6,1=>0x8503b77bf86e790629eb5db3452e88516354eb6f4ceab491cc46db2
|7,0=>0xe079b8c2ae702406336661c1756d465550e52a4050807403af3f7ab3cc033689c2baaa28e09286d7273f4228f920546202071ff5e1f96a1f3e11e3461db951bb6d1a6d41961b188a1183ec17ffe17dbf16a8f15525149e41408313adb139b11349012e2210aea0fad30f2bd0eb1c0c7db0b3b00a1fd09c9e0963c0886007dd3074fe06a99065a40611b0418403fd703cfd039d8034b902c67027ec026910260b021d7021610202501b510148400c8600af3005bd00568
|8,0=>0xe079b907607300e2964225904201f41be66149e40c7db040dd
|9,0=>0xe079b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0d0c0f0f0d0ca0a0a0a0000000000000000000000000a0a0a0a0000000050505050a0a0a0a0000000000000000050505050a0a0a0af0f0f0f0a000a0000000000000000000f0f0f0f0a000a00f0f0f0f0505050500000000000000000f0f0f0f00000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0c0f0c0f0c0f0c00000000000000000a080a080a080a08f0f0f0f0a0a0a0a00000000000000000f0f0f0f0a0a0a0af0e0f0e0f0e0f0000000000000000000f0e0f0e0f0e0f00f0f0f0f0f0f0f0f00000000000000000f000f000f000f00f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0af0f0f000f0f0f0000000000000000000a0a0a000a0a0a00f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0c0c0c0c00000000000000000f000f000c000c00f0c0f0c0f0c0f0c00000000000000000f0c0f0c0f0c0f0cf0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0ae0e0e0e0e0e0e0e00000000000000000e000e000e000e00f0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0e0000000050e050e000000000000000000000000050e050ef0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0cf0c0f0c0f0c0f0c00000000000000000f0c0f0c00000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f00000f0f000000000000000000000f0f00000f0f0000f0f0f0f0f0f0f0f00000000000000000000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c00000000f0e0f0e0000000000000000000000000f0e0f0e50e050e050e050e0000000000000000050e050e050e050ea0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000f000f000f000f0000000000000000000f000f000f000f003030f0c03030f0c000000000000000003030f0c03030f0c000000000000000000000000000000003030f0c03030f0c
|0,1=>0xf0f0f0f0f0f000000000000000000000a0a0a0a0a0a000000000000f0c0f0c0000000000000000000000000f0c0f0c30303030303000000000000000000000303030303030000a0a0a0a0a020a0000000000000000000a0a0a0a0a020a00f0a0f0a0f000f0000000000000000000f0a0f0a0f000f00b000b000b000b0000000000000000000b000b000a000a00f0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0ce0e0e0e0e0e000000000000000000000e0e0e0e0e0e0000f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0000f0f0f0f0f0f0f0f00000000000000000a000a000a000a00e0e0e000e0e0e0000000000000000000e0e0e000e0e0e0000000000000000000000000000000000f0f0f0e0f0f0f0ee0e0a0a0e0e0a0a00000000000000000e0e0a0a0e0e0a0af0f0f000f0f0f0000000000000000000f0f0f000f0f0f00f0f0a0a0f0f0a0a00000000000000000f000a000f000a00f0f0f0f0c0c0c0c00000000000000000a0a0a0a08080808c0c0f0c0c0c0f0c00000000000000000c0c0f0c0c0c0f0c00000000000000000000000000000000f0f0f0c0f0f0f0cf0f0c0c0f0f0c0c00000000000000000f0f00000f0f0000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f0f0050505050505050000000000000000000505050505050500f000f000000000000000000000000000f000f0000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a50505050f0f0f0f0000000000000000050505050a0a0a0af0f0a0a0f0f0a0a00000000000000000a0a0a0a0a0a0a0af0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000f0c0f0c0c0c0c0c00000000000000000f0c0f0c0c0c0c0cf0f0f0c0f0f0c0c00000000000000000f0f0f0c0f0f0c0cf0e0f0e0000000000000000000000000f0e0f0e0000000050505050000000000000000000000000d0d0d0d0c0c0c0cf000f000f040f0400000000000000000f000f000f040f04f000f000f000f0000000000000000000f000f000e000e00
|0,2=>0xf0f0f0f0f000f0000000000000000000f0f0f0f0f0c0f0c00000000000000000000000000000000f000f000f000f0030300000303000000000000000000000303000003030000f0f0f0f0303000000000000000000000f0f0f0f03030000f0c0f000f0c0f0000000000000000000f0c0f000f0c0f00f0f0a0a0f0f000000000000000000000f0f0a0a0f0f0000f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0000f0f0f0f0f0f0f0f00000000000000000f0f02020f0f020200000000f050f050000000000000000000000000f000f0000f000a000f000a0000000000000000000f000a000f000a00000000000000000000000000000000a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c00000000000000000e0e0e0e0e0e0e0e0000000000f000a000000000000000000000000000f000a3030303030303030000000000000000020202020202020200000000000000000000000000000000c0c0c0c0c0c0c0cc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c000030300000b0b0a0a0000000000000000030300000b0b0a0a5050505050505050000000000000000000000000000000000f000f000f000f0000000000000000000f000f000a000af0f00000f0f000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f00000000f0f00000f0f00000000000000000f0f0f0f0f0f0000c0c00000c0c000000000000000000000c0c00000c0c0000f0f0f0c0f0f0f0c00000000000000000f0f0f0c0f0f0f0cf0f0f0f0f0f0f0f00000000000000000c0c00000c0c0000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0a000000c0000000c00000000000000000404040c0404040cf0f0c0c0f0f0c0c00000000000000000f0f0c0c0f0f0c0cc0c0c0c0c0c0c0c0000000000000000000000000000000000000000f000f0e0000000000000000000000000f000f0e00f000f0f000f000000000000000000000f000f0f000f00
|0,3=>0xa0a0a0a0000000000000000000000000a0a0a0af0f0f0f0f0f0f0f0000000000000000000000000a0a0a0a101010101010000000000000000000001010101010100000000e0e00000e0e000000000000000000000e0e00000e0ef0f0a0a0c0c080800000000000000000f0f0a0a0c0c0808e0e0e0e0c0c0c0c00000000000000000e0e0e0e0c0c0c0c3030c0c03030c0c000000000000000003030c0c03030c0cf0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0000f0f0f0f00000c0c00000000000000000f0f0f0f00000c0c00f0000000f00000000000000000000000f0000000f0000f0f0f0f000f000000000000000000000f0f0f0f000f0000f0f0f0f0a0f0a0a00000000000000000f0f0f0f0a0f0a0a00000000a0a0a0a00000000000000000f0f00000f0f0a0a0000c0c00000c0c000000000000000000000c0c00000c0cf0003000f00030000000000000000000f0003000f00030000c000c000c000c0000000000000000000c000c000c000cf0f0f0f000c000c00000000000000000f0f0f0f000c000cf0f0f0f0e0e0a0a00000000000000000f0f0f0f0e0e0a0ae0c0e0c0e0c0e0c00000000000000000e0c0e0c0e0c0e0cf0f0f0f0f0f0f0f00000000000000000e0c0e0c0e0c0e0c303030203030302000000000000000003030302030303025050505050405040000000000000000050505050504050400f000f000f00000000000000000000000f000f000f0000f0a0f0a0a0a0a0a00000000000000000f0a0f0a0a0a0a0a50405040504050400000000000000000504050405040504f0f0f000f0f000000000000000000000f0f0f000f0f00000000000000f000f000000000000000000000000000a000a00f000f000000000000000000000000000f000f00000000c0f0c0f0c0c0c0c00000000000000000c0f0c0f0c0c0c0cf0f0f0f0f0f0f0f00000000000000000d0c0d0c0d0c0d0ca000a000a000a0000000000000000000a000a000a000a00a0a0a0a0a0a0a0a00000000000000000a0a08080a0a0808
|0,4=>0xf0f0f0f0c0c0c0cf0f0f0f0f0f0f0f00000000000000000303030003030300f000f000f000f0000000000000000000f0f0f0a0f0f0f0a0000c0c00000c0c00000000000000000c0c0c0c0c0c0c0c00a000a000a000a0000000000000000000f000a000f000af000f0e0f000f0e00000000000000000f000f0e0f000f0ec0f0c0e0c0f0c0e00000000000000000c0f0c0e0c0f0c0e00000000f000f0f0000000000000000000000000f000f00000000000000f0f00000000000000000000000000000f00f0f0f0f0f0f0e0e00000000000000000f0f0f0f0f0f0e0e00000000000000000000000000000000f0f00000f0f0000f0f0f0f0f000f0000000000000000000f0f0f0f0f0f0f000000f0f00000f0f000000000000000000000f0000000f002020a0a02020a0a000000000000000002020a0a02020a0a0000300000003000000000000000000000003000000030000000000000000000000000000000000f0f0f0f0f0c0f0c0000f0c00000f0c000000000000000000000f0c00000f0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000e0e0e0e5050505040404040000000000000000050505050404040400000000000000000000000000000000f0f0f0f0f0a0f0a00000000000000000000000000000000f0f0f0f000000000000f0f00000c0c000000000000000000000f0f00000c0c00a000a0a0a0a0a0000000000000000000a000a0a0a0a0a00a000a000a000a0000000000000000000a000a000a000a0000f0f00000f0f000000000000000000000a0a00000a0a00f00000f0f00000000000000000000000f00000f0f0000f0c0f0c0f0c0f0c00000000000000000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000000020200000202f0f0a000f0f0a0000000000000000000f0f0a000f0f0a0000000000404040400000000000000000000000004040404f000f000b000b0000000000000000000f000f000b000b00
|0,5=>0xc0c0c0c0c0c0c0c00000000000000000c0c0f0f0c0c0c0cc000c000c000c0000000000000000000c000c000c000c0030c030c030c030c0000000000000000030c030c030c030cf0f0f0f0f0f0f0f00000000000000000303030303030000f0f0f0f0f0f0f0f00000000000000000c0c0e0e0c0c0e0ef000f000f000f0000000000000000000300030003000300f0f0f000f0f0f0000000000000000000f0f03000f0f0300f0f0f0f0f0f0c0c00000000000000000f0f0f0f0f0f0c0c2020202020202020000000000000000020202020202020230303030303030000000000000000000303030303030300f0f0f0f0c0c000000000000000000000f0f0f0f0c0c0000f0f00000000000000000000000000000f0f0000000000000000f0f0f0f0000000000000000000000000f0f0f0f0000f0f0f0f0f0f0f0f00000000000000000f0a0f0a0f0a0f0af0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e0000f0f00000f0f000000000000000000000e0e00000e0e0000000000000000000000000000000000f000a000f000af0f0f0f0e0e0e0e00000000000000000f0f0f0f0e0e0e0e0000a0a00000a0a000000000000000000000a0a00000a0ac0c0e0e0c0c0e0e00000000000000000c0c0e0e0c0c0e0ec0f0c0f0c0f0c0f00000000000000000c0f0c0f0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0e0e0f0f0e0e00000000f0f0f000000000000000000000000000f0f0f00f0f0f0f0f0f0f0f0000000000000000000000000f0f0f00c0c0c0c0f0f0f0c00000000000000000c0c0c0c0f0f0f0cf030f000f030f0000000000000000000f030f000f030f00a0a00000a0a000000000000000000000a0a00000a0a00005050a0a05050a0a000000000000000005050a0a05050a0a00000000303030000000000000000000000000003030300f000f000f000f0000000000000000000f0f0f000f0f0f00a0f0a0f0a0e0a0e00000000000000000a0f0a0f0a0e0a0ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0c
|0,6=>0x50005000f000f000000000000000000050005000f000f00f0f00000f0f0a0a00000000000000000f0f00000f0f0a0af0f0f0f00000000000000000000000000000000000000000000f0000000f00000000000000000000000f0000000f0000400040004000400000000000000000004000400040004303030303030303000000000000000003030303000000000000f0f00000000000000000000000000000f0f00000000c0c0f0f0c0c0c0c00000000000000000c0c0f0f0c0c0c0c5050000050500000000000000000000050500000505000000000000f0f0a0a0000000000000000000000000f0f0a0ae0e0e0e0e0e0e0e00000000000000000a0a0a0a0a0a0a0ab000b000b000b0000000000000000000b000b000b000b000000f0f00000f0f0000000000000000000000000000000040404040404040400000000000000000404040404040404f040f040f040f0400000000000000000f040f040f040f0430303030000000000000000000000000303030300000000f0f03030f0f000000000000000000000f0f03030f0f000000000000c0c0c0c0000000000000000000000000c0c0c0c30003000300030000000000000000000f000f000f000f00c0c0c0c0000000000000000000000000c0c0c0c00000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0000000080c080c080c080c0000000000000000080c080c080c080c50505050000000000000000000000000505050500000000f0f0f0f0f0f0f0f0000000000000000050505050000000040c040c040c040c0000000000000000040c040c040c040c50005000500050000000000000000000500050005000500f0f05000f0f050000000000000000000f0f05000f0f05000000a0a00000a0a00000000000000000a0a0a0a0a0a0a0af0c0a080f0c0a0800000000000000000f0c0a080f0c0a08f0f0f0f0f0f0f0f00000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000003000000030020202020202020200000000000000000a0a0a0a0a0a0a0a
|0,7=>0xf0f0f0f0f0a0f0a00000000000000000f0f0f0f0f0a0f0af0f0f0f000000000000000000000000030303030000000030300000f0f00000000000000000000030300000f0f000030003000300030000000000000000000300030003000300f0f0f0f0f0f0a0a00000000000000000f0f0f0f0f0f0a0a00000000000000000000000000000000300030003000300c0c0f0f0000000000000000000000000c0c0f0f00000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2e0302102d1a0708092c2b2a0903111a1016070209082807130927020a08042602252409070223081002091003072209080304072109080304072003070904021f09021d07080c0911041c080c09070402161b09031a1916080918071703071615140904131211090311100f0908070e0d09040c0b0a09080706050403020100
|1=>0x8090244080226431a18042d0c02030a08070409024104094008070c02080918073807020815033f0408023e093d08020307093c093b1807080c09080307043a02081a391526080207150338020309070437030832331109031104360c0803041109350302090704340308320433110307320408310902081a0330040302092f
|2=>0x1a040809075b030a040713094c020a070203045a085903020704090858090704080203570308071104095609020708041b29020308045409430708030204095303090204525102040309084b500802070904034f0907041b02160709080403024d080907040206020704034b4a040302484702031a10464309070829450a0304
|3=>0x802070904036e09030402086d6c0709041013020a0308020904076b0809020703046a04070902690813080709260268090802046703390908071c450403026607080c0907040803026504080932030763030907080204620904021c08070c030209070804600409030208075f0403070948085e0408021109035c0309021042
|4=>0x430308071104820908040307800207094604037e0802070403097d0302081007097c0208030709047b090807020e03180209081003077a0408030279070403020908780802041a0903770908040307210803020445725d080709026904180408021139092608070209047574070203040809730308043207710809041a02036f
|5=>0x80302092f0208030418725d02081a033909150709041003028e08090704021a230903071a1002160902080304078d0209081a03398c0907020403088b0204088a070989080203880907430903110487080c07020804860326080407260285030904100784070203045a08460307320445084603020709040883020803045a07
|6=>0x89e040309072f08160703090408029d0308099c04024508042a0a0907430703080904029b0803070409029a03080409020799030802090704350308023207043304070908020398040709030208970208030904079607040302080994030407110809930807099203020a07020908291e040309079108160409020703089004
|7=>0x704090208af080904027003ae020308100907ac040903080207ab020304070809aa070409020308a8090413070c0264040809020307a7080403260702a60809021104038108030207a40204037a080946080402090703a30408072d03020a030704450809a2080903070204a10902040307a09f0802092607048c0304020907
|8=>0x408030911bd02090407b10313020403090850040209030708bc0208041a390926020308070904bb080209030407380304080702b90804020326078903021007b70946080409030207b608020907b5046e02070408b30402032643080c03076145090846040802115d03260803020715a403070408b20932030204080710b003
|9=>0x207040308c8020708092604180803090204c7030807040209c507040803020985020703080904c408030902046d080907040206080311095d0487030807020409c3020904070803c2030408070902c1020409084b07390203040708b1b007020410130926090807450a18090807c002030a020408090307bf0802032643041a
|10=>0x803020a0409d7020708040903d6020903080704d50903080407d407020304180908d3040302090747090308040702d1070203047f080995030204070c0946020908041a033902090804071a03ae080407090302262c080402070309cf040809021103ce0309040708cd0209040307cb090308040207ca08040207033909b809
|11=>0x100207080326090415070208030409de04070209dd1302090804cc390903040708021602070804091503d604080309022f08030207b709150902070813041e090408074203020a0309020408075203090407080284080309020407db030907084204024502070408030926090204080307da0408020907b5080402090307d807
|12=>0x460304070211090846040903020a08075104080302725d07040803dc76030902081007041a020708030904e2030907080c0204c60307020816090415090204081007033903090708100287020704032608d3030904070802e1080402070903e00803090704020e0709080304df070209081e18040702081309d9090207031304
|13=>0x807020409d70702090803041e040702030908d30903040708021602070408030926080309020704b7080309020704080907020403e6030802093207041a09020408d0ce0809020445030739090408070c03020a0904080751030264030907080c020445020904080703e50408020307e4090408031302071103040702e30908
|14=>0x80309020704080309020704020908040307cc0209030408070c040803090207be03
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x285046a07940ca814501ea029402a8005
|5,0=>0x1196226c439484310261f8c3d987830ea61c8c37986c30d26198c31986030ba6168c2b9854a8a3613ac25d848b08b610ac1fd83d287460dcc1a5431b05d60aec145825b045607ec0e5819b02d6
|6,0=>0x594eb0dd5e3ab5755cea9dd50b29b6528ea35d433a7f74f2c9cd9363a6574bce95dd283a497488a8f5d1b3a306452e889d0dba14741ae81d90039f973e4e7adcf239dd73ace7418e4b9c4537ae6d9cd7b9a87342e669cc9b98c730ae5fd8bc397172d4e58dcae3955729ce51dca0393a6266e4b1c93311f7
|6,1=>0x900f1e9a39bc6d68ccf17de2c3c517896d111e1ebc36785ef0a9611bc1c782af03da043c0177f4efcddf63be577bcef5dde83bc97784eeedddb2baf7750ee85dcd3b937718ee15dbf3b7776e0eda5db13b5b76a8ed35da33b3f7670ecc5d953b237638ec55d87b3087602ebed97a3aed75cceb7dd6c3ad17
|6,2=>0x1331a62bcbe796ef2c1e54bca27936f255a473c877
|7,0=>0xd1eda1e33fc6778cdf19a5b31b65b8ca8f932322463c8c6af8b9f13be207c32f84db06b6067bfef7de2f83dea6bc8d775eeac5cf6b90f705edcc5b27b56f691ece45957b1cf621ac0bd798ae4f5adeb2b55d8aaed541ea445417a74f4ca29545237a38f459a8835097a0313e9e79bced69ccf37de6c3cd26
|7,1=>0x6d16d94fb0a35e36b48d591a9234e46957
|8,0=>0x38b370f7e10fc05f7d3ef37dd8fb95f6f3ed77
|9,0=>0x71c6
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 231 then fld (dictB (i / 512) (i / 32 % 16)) 188 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 8 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 15 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x91e40c1002158102507024106d034e41022090741d5508048201e071081021074b02099030940821034e410224b4cc2024082640c2508494241c09114081d09074242108044101d02034081104134200d03044101d09074240d020341c21094241c200807428ab030240c0807084100d021e4100c080242011040741c09291ec0c1003104201107084607b04034100c
|1=>0x3044089a09034240d07034081d047540dd90209809cb0709c082503704081e070440ccd044941c24086d41d8504020080d03084201103084089a0903410a902030240d0307410460702410090361410080708424a9030202842030241021076440c0b09024201d036141008080282445020740d750907c081d040741c20040840c0902494241c030242420030856821
|2=>0x7044082108044101d131a8101d08034e41307034101d0907410ab020301c210402c1c090903440270804424ab02030240d024241c20040842421091e40c10090840811020941c25091e40c10096141008070240a0718078100d087f4100f080946827070441021030441045070241c790304020114349c241d090702199092a40c08037241c27070441c26090780811
|3=>0x907c240d18078100d020745697090442410080941c7904030c8e7070340825030242509080700a55080981009a008c4c1d08034e41303074240d040241d3308090241d02034080c07564540b04094c868070440825044941c24020942a55080980c091609c0821070240c090449c1c24030400c41080441e3d09118081d0907c241e030444c090308420110e0300869
|4=>0x2034110b0807046fb02074081c030842069040741d2c082640c25083d4981f0903432b509048201d261a0101d0903426e90251c201eb809c981d090342025070481021b50440d25090709ad3030940c2408074241d09034242102044081009034241f02074569709044241009024400904086c42707104102107ad410270804422a50332824090302c201d080340975
|5=>0x7d94240e040980c091503c102504424201c02d2c101e090880c1108494241c02d24101e080980c12090841c2107034101d1a034101d02264240d09d041c0e0703c081d0242c1c2008cc40c1c07c6c100a390941c0d08c94100e030440c250761c081009c64100a092ac0c08044cc20240761408100703420990309426c6081a4101d090340c21080440c11030241009
|6=>0x7098241e0902c240a070441021260440c250204c1c210904408210703410210402c10210809c0c250c0281c21035dc1c26021a41c11021ec0c10030440c10090380c2104084200d090440c25097f40c12030840c20030740c1c08024540f040941f7109028241107048100c080340c09080701c4204084090907081141e020441009070800c251307c200d03494241c
|7=>0xc1c08074081c040980c10090882009030941c12450340811070440825030781c0e03074081103024201d0302c201e020441c210351c201e09ccc0c1c02074200d090841c0a090841c09080780c09
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x14209104081c4000061028800008200000000000000310000000000000000000000000000000000000000000000042011000000000000000000000000010000000
|6,0=>0x5b18000000b33581ab4d546a73521a84c0009e34d9a60d2a600049180011e68c3449a18d0660004019f4cf467730001d0ce266e33599a0c000000329988cbe65c32c9958ca6600028180000004d325191cc8864131f180000003b31c18d4c0003231798000586000
|6,1=>0x4e8e6e734398980025c72b3941c94e4460008f9c70e327163899c40e1a70a300000020e6000000410e0260007f1becdf06f53791bbcdd86000749b98c00000000038cdc06000000374db46d730000000000d43689b38d966000000320d8a6000611afcd786b93
|6,2=>0x2927463a19d00e7a6000
|7,0=>0xe41718b885c22e016f8b785ba2dc16d8b685b22d816b8b585aa2d41698b485a22d01678b3859a2cc165c72a5932c8963cb1a58b2c4961cb0a5841c11600afc57c2bd15e0aec5742b915c0adc56c2b515a0acc5642b11580abc55c2ad1560aac5542a91540a9c54c2
|7,1=>0x1da0ec1758ba85d22e81738b985ca2
|8,0=>0x3c61e21f08f807be3de1ee8f707b63da1
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 13 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x240003000240000400000000801000000001000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000090000c1000000000000000000000000000000001000000000000
|6,0=>0x74200a00030002000000000c000180008010008020000000040000d8000c0020002000009c102000020000000000000c00000000000040000040000021000004002700200001400400000120000080880010000000000000000200010000000000000004000500404000000000000000800000400004000304000000000080004000000000100004000900008000004000000000400000800008000562210202004004000000010024204004202004000000800000000200120054c00800000200000004000004001400004000000034400100100004000040000000000002003004000200b0c0100000400004000000040000000000000200210003102010080400080000000000000100003040101000002102004000000028800000
|6,1=>0x40001000220004c0001000000
|7,0=>0x1f01300014000e4800c001802401000900079200e68060002410090011009520a0153032014270042040010002800c307023801d100d9814f0130554c3020c908aa810088027200e9001e000e77002404c4c0070300411100023c09558003c2041000db783e01520801e4804480270251e000f0c20a05482843c0480240b2005a00109061011079011e08056600e480746404030e9140320038733500095c007a4b084
|8,0=>0x3fac079200c8807460272530518a8a00e644364003c1
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 18 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_186,6,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 1 then [(dom_185,6,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 2 then [(dom_179,6,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 3 then [(dom_171,6,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 4 then [(dom_155,6,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 5 then [(dom_59,6,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 6 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 7 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 8 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 9 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 10 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 11 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 12 then [(dom_184,4,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 13 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])++(if pm.testBit 14 then [(dom_177,4,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 15 then [(dom_163,4,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 16 then [(dom_139,4,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 17 then [(dom_27,4,runOps true dom_27 (0,roots_27) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_187 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_186 _ g hchk
    · exact cpcs (by decide +kernel) low_185 _ g hchk
    · exact cpcs (by decide +kernel) low_179 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_155 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) low_57 _ g hchk
    · exact cpcs (by decide +kernel) low_147 _ g hchk
    · exact cpcs (by decide +kernel) low_43 _ g hchk
    · exact cpcs (by decide +kernel) low_184 _ g hchk
    · exact cpcs (by decide +kernel) low_58 _ g hchk
    · exact cpcs (by decide +kernel) low_177 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
    · exact cpcs (by decide +kernel) low_27 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_186 6 s (0, roots_186) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_186 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffffffff00000000ffffffff00000000, 96)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccccccccccccccccccccccccccc, 126), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_187 == dom_187) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_187 goalM v ys) : RunD true dom_187 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_187 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_24 : ∀ i, 24 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_36 : ∀ i, 36 ≤ i → i < 41 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 36 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 41 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_12) z5_24) z5_36)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_132 : ∀ i, 132 ≤ i → i < 139 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 132 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 139 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108) z6_120) z6_132)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_12 : ∀ i, 12 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_24 : ∀ i, 24 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_36 : ∀ i, 36 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_48 : ∀ i, 48 ≤ i → i < 60 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_60 : ∀ i, 60 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_72 : ∀ i, 72 ≤ i → i < 73 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 72 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 73 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_187 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_187 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_187 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_187 roots_187 goal_187 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_187

theorem low_187 : Lower true dom_187 roots_187 goal_187 10 := S_187.noCircuit

namespace S_120
def pairsG : List (Nat × Nat) := [(8,40), (8,72), (16,80), (24,56), (24,88), (32,40), (48,56), (48,112), (64,72), (64,80), (96,104), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_120.map (· &&& dom_120)
def goalM : Nat := goal_120 &&& dom_120
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x6780b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x8080808080808080000000000000004040404000000000404040400000002020000020200000202000002020001000100010001000100010001000100
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 121 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_120 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_120 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_120 == dom_120) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_120 goalM v ys) : RunD true dom_120 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_120 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_120 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_120 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_120 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_120 roots_120 goal_120 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_120

theorem low_120 : Lower true dom_120 roots_120 goal_120 4 := S_120.noCircuit

namespace S_114
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (16,18), (16,80), (32,34), (48,50), (48,112), (64,80), (66,82), (66,98), (96,98), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_114.map (· &&& dom_114)
def goalM : Nat := goal_114 &&& dom_114
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xf2e14
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa000a000a000a000000000000000140014000000000014001400000002800000028000000280000002800040004000400040004000400040004
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 115 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_114 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_114 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_114 == dom_114) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_114 goalM v ys) : RunD true dom_114 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_114 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_114 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_114 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_114 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_114 roots_114 goal_114 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_114

theorem low_114 : Lower true dom_114 roots_114 goal_114 4 := S_114.noCircuit

namespace S_106
def pairsG : List (Nat × Nat) := [(2,34), (8,40), (8,72), (10,42), (10,74), (32,34), (32,40), (64,72), (66,74), (66,98), (96,98), (96,104)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_106.map (· &&& dom_106)
def goalM : Nat := goal_106 &&& dom_106
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xf0afa
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a00000a0a000000000000000141400000000000014140000000280000002800000028000000280404000004040000040400000404
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 107 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_106 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_106 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_106 == dom_106) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_106 goalM v ys) : RunD true dom_106 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_106 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_106 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_106 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_106 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_106 roots_106 goal_106 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_106

theorem low_106 : Lower true dom_106 roots_106 goal_106 4 := S_106.noCircuit

namespace S_90
def pairsG : List (Nat × Nat) := [(2,18), (8,72), (10,26), (10,74), (16,18), (16,80), (24,26), (24,88), (64,72), (64,80), (66,74), (66,82)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_90.map (· &&& dom_90)
def goalM : Nat := goal_90 &&& dom_90
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x3a8c5
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a0a0a000000000000000141400000000000014140002800280000000000280028040404040000000004040404
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 91 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_90 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_90 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_90 == dom_90) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_90 goalM v ys) : RunD true dom_90 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_90 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_90 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_90 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_90 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_90 roots_90 goal_90 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_90

theorem low_90 : Lower true dom_90 roots_90 goal_90 4 := S_90.noCircuit

namespace S_122
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (8,40), (8,72), (10,26), (10,42), (10,74), (16,18), (16,80), (24,26), (24,56), (24,88), (32,34), (32,40), (48,50), (48,56), (48,112), (64,72), (64,80), (66,74), (66,82), (66,98), (96,98), (96,104), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_122.map (· &&& dom_122)
def goalM : Nat := goal_122 &&& dom_122
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xb4b8b29ba2
|5,0=>0xefe432a1e10b106
|6,0=>0xefe43
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x5050505050505050505000005050000a0a0a0a0a0a0a0a0a0a0a0a0000000140014001400140014001400140014000002828000028280000202000002025050000050500000505000005050000808080808080808080808080808080941414141414141400000000000000028282828000000002828282800000005000500050005000500050000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x21463214636312484632171632543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x5960ca6
|6,0=>0x1b5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 9 then fld (dictB (i / 512) (i / 32 % 16)) 123 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 9 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x24485
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x441
|6,0=>0x20
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 6 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x88
|6,0=>0x1f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_120,4,runOps true dom_120 (0,roots_120) ops)] else [])++(if pm.testBit 1 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 2 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 3 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 4 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_122 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_120 _ g hchk
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_90 _ g hchk
    · exact cpcs (by decide +kernel) low_58 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_120 4 s (0, roots_120) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_122 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_120 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_122 == dom_122) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_122 goalM v ys) : RunD true dom_122 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_122 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_122 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_122 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_122 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_122 roots_122 goal_122 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_122

theorem low_122 : Lower true dom_122 roots_122 goal_122 7 := S_122.noCircuit

namespace S_81
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (16,17), (16,80), (64,65), (64,80)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_81.map (· &&& dom_81)
def goalM : Nat := goal_81 &&& dom_81
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x9e3d8
|3,0=>0x9e3d8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x300030000000000000000c000000000000000c000200020000000000020002
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 82 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_81 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_81 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_81 == dom_81) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_81 goalM v ys) : RunD true dom_81 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_81 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_81 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_81 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_81 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_81 roots_81 goal_81 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_81

theorem low_81 : Lower true dom_81 roots_81 goal_81 4 := S_81.noCircuit

theorem low_113 : Lower true dom_113 roots_113 goal_113 5 :=
  lower_slice (d:=dom_113) (dSub:=dom_81) (T:=goal_113) (TSub:=goal_81) (roots:=roots_113) (rootsSub:=roots_81)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30003000000000003000300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_81

namespace S_73
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (8,9), (8,72), (64,65), (64,72)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_73.map (· &&& dom_73)
def goalM : Nat := goal_73 &&& dom_73
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xbc96e
|3,0=>0xbc96e
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3030000000000000000c000000000000000c02020000000000000202
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 74 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_73 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_73 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
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

theorem low_73 : Lower true dom_73 roots_73 goal_73 4 := S_73.noCircuit

theorem low_105 : Lower true dom_105 roots_105 goal_105 5 :=
  lower_slice (d:=dom_105) (dSub:=dom_73) (T:=goal_105) (TSub:=goal_73) (roots:=roots_105) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000030300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_73

theorem low_89 : Lower true dom_89 roots_89 goal_89 5 :=
  lower_slice (d:=dom_89) (dSub:=dom_81) (T:=goal_89) (TSub:=goal_81) (roots:=roots_89) (rootsSub:=roots_81)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30003000000000003000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_81

namespace S_121
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (1,65), (8,9), (8,40), (8,72), (16,17), (16,80), (24,25), (24,56), (24,88), (32,33), (32,40), (48,49), (48,56), (48,112), (64,65), (64,72), (64,80), (96,97), (96,104), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_121.map (· &&& dom_121)
def goalM : Nat := goal_121 &&& dom_121
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xa44c8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3030303030303030000000000000000c0c0c0c000000000c0c0c0c00000003030000030300000303000003030000c000c000c000c000c000c000c000c02020202020202020202020202020202
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 122 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 3 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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

def pmB : Nat → Nat → Nat
|6,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 4 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 1 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 2 then [(dom_89,5,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 3 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_121 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_113 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_89 _ g hchk
    · exact cpcs (by decide +kernel) low_57 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_113 5 s (0, roots_113) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_121 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_113 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_121 == dom_121) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_121 goalM v ys) : RunD true dom_121 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_121 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_121 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_121 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_121 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_121 roots_121 goal_121 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_121

theorem low_121 : Lower true dom_121 roots_121 goal_121 7 := S_121.noCircuit

theorem low_105_l32 : Lower true dom_105 roots_105 goal_105_l32 5 :=
  lower_slice (d:=dom_105) (dSub:=dom_73) (T:=goal_105_l32) (TSub:=goal_73) (roots:=roots_105) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000030300000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_73

theorem lowZ_105_2_32 : Lower true dzo_105_2 roots_105 gzo_105_2_32 5 :=
  lower_iso (d1:=dom_105) (roots1:=roots_105) (T1:=goal_105_l32) [(dom_105, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_105_l32

namespace S_99
def pairsG : List (Nat × Nat) := [(1,33), (1,65), (2,34), (3,35), (3,67), (32,33), (32,34), (64,65), (66,67), (66,98), (96,97), (96,98)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_99.map (· &&& dom_99)
def goalM : Nat := goal_99 &&& dom_99
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x5cff8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0000000f0000000000000000f000000000000000f00000000c0000000c0000000c0000000ca0000000a0000000a0000000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 100 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_99 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_99 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_99 == dom_99) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_99 goalM v ys) : RunD true dom_99 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_99 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_99 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_99 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_99 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_99 roots_99 goal_99 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_99

theorem low_99 : Lower true dom_99 roots_99 goal_99 4 := S_99.noCircuit

namespace S_107
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,34), (3,11), (3,35), (3,67), (8,9), (8,40), (8,72), (10,11), (10,42), (10,74), (32,33), (32,34), (32,40), (64,65), (64,72), (66,67), (66,74), (66,98), (96,97), (96,98), (96,104)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_107.map (· &&& dom_107)
def goalM : Nat := goal_107 &&& dom_107
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xff354
|5,0=>0x9349b
|6,0=>0xde658
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f00000f0f0000000000000000f0a00000f0a00000f0a00000f0af0f0000000000000f0f00000000c0c00000c0c00000c0c00000c0cf0000000f0000000f0000000f00a0a00000a0a00000a0a00000a0a0000000000000000f0a00000f0a
|_,_=>0
def stPool : Nat → Nat
|0=>0xd133a346c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 108 (i % 32) else 0
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
|0=>0x45
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x1
|6,0=>0x10
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0xf
|6,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 1 then [(dzo_105_2,5,runOps true dzo_105_2 (0,roots_105) ops)] else [])++(if pm.testBit 2 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 3 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 4 then [(dom_99,4,runOps true dom_99 (0,roots_99) ops)] else [])++(if pm.testBit 5 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_107 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_105_2_32 _ g hchk
    · exact cpcs (by decide +kernel) low_43 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_99 _ g hchk
    · exact cpcs (by decide +kernel) low_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_105 5 s (0, roots_105) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_107 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_105 h

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_107 == dom_107) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_107 goalM v ys) : RunD true dom_107 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_107 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_107 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_107 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_107 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_107 roots_107 goal_107 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_107

theorem low_107 : Lower true dom_107 roots_107 goal_107 7 := S_107.noCircuit

theorem low_89_l16 : Lower true dom_89 roots_89 goal_89_l16 5 :=
  lower_slice (d:=dom_89) (dSub:=dom_73) (T:=goal_89_l16) (TSub:=goal_73) (roots:=roots_89) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000000000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_73

theorem lowZ_89_2_16 : Lower true dzo_89_2 roots_89 gzo_89_2_16 5 :=
  lower_iso (d1:=dom_89) (roots1:=roots_89) (T1:=goal_89_l16) [(dom_89, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_89_l16

theorem low_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (d:=dom_83) (dSub:=dom_81) (T:=goal_83) (TSub:=goal_81) (roots:=roots_83) (rootsSub:=roots_81)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c00000000000c000c, 16, 18)] (by decide +kernel) (by decide +kernel) low_81

namespace S_91
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,65), (2,18), (3,11), (3,19), (3,67), (8,9), (8,72), (10,11), (10,26), (10,74), (16,17), (16,18), (16,80), (24,25), (24,26), (24,88), (64,65), (64,72), (64,80), (66,67), (66,74), (66,82)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_91.map (· &&& dom_91)
def goalM : Nat := goal_91 &&& dom_91
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x462f8
|5,0=>0xeadf9
|6,0=>0x3f37a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f00000000000f000f00f0f0f0f000000000a0a0a0af0f0000000000000f0f0000c0c0c0c000000000c0c0c0cf0f0f0f0000000000000000a0a0a0a000000000a0a0a0a00f000f00000000000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0x53333346c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 92 (i % 32) else 0
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
|0=>0x45
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x1
|6,0=>0x10
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 5 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0xf
|6,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_89,5,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 1 then [(dzo_89_2,5,runOps true dzo_89_2 (0,roots_89) ops)] else [])++(if pm.testBit 2 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 3 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 4 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])++(if pm.testBit 5 then [(dom_27,4,runOps true dom_27 (0,roots_27) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_91 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_89 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_89_2_16 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
    · exact cpcs (by decide +kernel) low_90 _ g hchk
    · exact cpcs (by decide +kernel) low_73 _ g hchk
    · exact cpcs (by decide +kernel) low_27 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_89 5 s (0, roots_89) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_89 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_91 == dom_91) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_91 goalM v ys) : RunD true dom_91 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_91 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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

theorem low_91 : Lower true dom_91 roots_91 goal_91 7 := S_91.noCircuit

theorem low_121_l48 : Lower true dom_121 roots_121 goal_121_l48 6 :=
  lower_slice (d:=dom_121) (dSub:=dom_105) (T:=goal_121_l48) (TSub:=goal_105_l32) (roots:=roots_121) (rootsSub:=roots_105)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030000030300000303000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_105_l32

theorem lowZ_121_2_48 : Lower true dzo_121_2 roots_121 gzo_121_2_48 6 :=
  lower_iso (d1:=dom_121) (roots1:=roots_121) (T1:=goal_121_l48) [(dom_121, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_121_l48

theorem low_115 : Lower true dom_115 roots_115 goal_115 6 :=
  lower_slice (d:=dom_115) (dSub:=dom_113) (T:=goal_115) (TSub:=goal_113) (roots:=roots_115) (rootsSub:=roots_113)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c000c000c000c000c, 16, 18)] (by decide +kernel) (by decide +kernel) low_113

namespace S_123
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (1,65), (2,18), (2,34), (3,11), (3,19), (3,35), (3,67), (8,9), (8,40), (8,72), (10,11), (10,26), (10,42), (10,74), (16,17), (16,18), (16,80), (24,25), (24,26), (24,56), (24,88), (32,33), (32,34), (32,40), (48,49), (48,50), (48,56), (48,112), (64,65), (64,72), (64,80), (66,67), (66,74), (66,82), (66,98), (96,97), (96,98), (96,104), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_123.map (· &&& dom_123)
def goalM : Nat := goal_123 &&& dom_123
def NN : Nat → Nat
|3=>0x1
|4=>0x16
|5=>0x9a
|6=>0x192
|7=>0x9c
|8=>0x12
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xdd59
|4,0=>0xe807ce3db8967a6933908cee27a6d0795d94f4b24b7244ab9733cbe30a0d2b55f2aec92a6472651e1b660172ae162ac0d1a208048041e7
|5,0=>0xb1eabb16b0ab5f1a7f33a46e7a1b379f9229ce319993695a9c926409243b8caa58c5958c3c88b0218aeb08a6c688151872758219780cc07d6487b92979e4178ee1775ae74c1f73de072ba371fab71eff70a536d3c16c90869da169a91694e669299639355e5a65e3035ddbb5a1065764c561d054edb5452b53c77510f050add502494fa144f6384c45f4a09c4923345ed544f2244e8644947442f841362410253fbaf3f1b43c0273bd973ab1a3984b3810237ab436cd2369883641734b67347b632a373183830e6e30cd13045c300282fe412e4422ddde2c0482b0792a45a2819225a6224dc324b302446222cc22178320bf61ec1b1e40e18f0e18b9316e6f16e2d15e95158081532a14529141ee13dcb13995137fc12682125681190c1120b1105a0f6410c9b10c3e50c1080ad6a0a833073710467b044290408e02a1b01358
|5,1=>0xf2ffdf2037f1501ef2d4e7da0e42ace03b9dc3b6d920ed618fd34e9d12dacd8e0c965cc74b0c5722c51abc349fc065fbefd0be598bb7ccbb78fb8b8bb7b7bb4f4c
|6,0=>0x28d9028957288042859d27ba12731f26e7f256c5255ca2511724e8f2465624409243932438c242ad23f6323987234e42321122b9c221e420df120956206bd2064920244201cb1fc841f96d1f8ae1f2721f0261dd621d47e1d4231d3ff1ca471c50b1c2d51bf9e1b4361ac491a75b1a4521a16919d05195541925818cfd1899d1708416e2d16da016b7f1642e15de415b8c1570a14ab813e2c13c2a13ade137fc1329b1300b121281203d11cc0113221120b10903108c5107c710495101380e7270df090da310d5430d28a0d2240ce530cab00c8340c7ce0be920b93c0b7dc0b3e90aa090a4ae0a4700a1ed09e3f09e1e09dd409b660993909936094c60946f090d308680072dd0715f063e60629c061ca05f9e05cad05c400536304c1d04490042ee040c103e3d03d29034ec026f10211d01f1d0185e00d9e009a600978000e0
|6,1=>0x6c4666a1396929d68fa468d0e67ac1676f067612665b76659a65d6a64f3263bf863a4e62f8b62abd61ef260e29605c35fed85e0965df985d97b5cd815c7ff5c5de5c50e5b7cd5a3385a2db5887f586f9577e5575d5573b255f6b5482c5475c5434653fc5532b452e3052b7b52a925192751556507035004d4fa144ec934e4464ce5a4ca9e4c9664c78d4aac94a85b49e2349c1c47b8846b9645d954597744d4f44bfc4494744791445534423c43be042b934228341ee941df44168d410763fbfd3f92a3f8f33f39b3f10c3ec723ea503e82a3e67c3d0cf3bdcf3b8573ae7e3a66c3a32039f0639dbc3999b388813823f380db379773761d370f736e773699e366b43657d3548033d32333f331f6331d3731d2730a6c2f8482f28b2f1132eecc2e33f2df7a2d7522c79d2c5fb2c0b02bd642b49e2a7af2a45029e3b290e3290a0
|6,2=>0xd1df5c8f72c899bc7de0c586ec4a56c460ac35eec2f9ac11d5c0d96bffbabf783bf4e0bdbf4bd36abbd39ba457b95ffb77c8b712ab615eb567eb5677b3f7bb30ecb2700b0c02b0840aeac5abd61aa227a8cf7a7d7da788da7575a745ca71cca5ae7a54d5a4f26a32c0a32a1a30f8a0489a03479ff229fcf79f48d9f2209dc5a9db499d9aa9cd949bf719ba609af969af5f9aaa89a01b96daf9679a966be96526964a595d939456593c149264491a7490f5c901568f3508f0cb8ea418e65b8e6338cf868b18c8ab0b889c388376877f586e2186e01862bc84b9f82a3982312818fe803187fb8e7f5eb7d6487d6367d5787d2e27cd8c7cbf17c7e37bf897b9047ab5f7aa437a7c679d707964c7939577ef077a32770c876a7675a73755c874b72741f572f7472c8d72c7d71a6d718ef70a2e6ff8e6feb96f2036eca56ea1f6e410
|6,3=>0xf4976f059cf01eeed117e8b5ce58fee0cdddfdf3df502de0b3dd0efda929d920ed4f58d4ba4d406ed2734d2327
|7,0=>0x9ea7f9d68997891970d19574c9368d922d991b939124f90c448d3df8ce618a1d08833785511823127fda97ebcf7eb857e62b7d5c87c7887916677732767db7468d7160d70f5a6f0106dbab6d40f6c9d36c1c46bc346ba9867dfd6712765f2165add6315e62cfc60e295e72c5cef45c49e5981159399592125835a57595573be56f1f56562532b451ab250ec84b20148fde475314680844b284412b3ef533ec723e82a3e4483cdb23c7ff3c1d83bb993b3423a3be3a22a366a735a893587534e1f33cb83354c31bc42e20d2d2082cf692cacc2b4cc2b4552acfe29a352981929250291582801c255ca253d7253932493d247cd224ad21a171cd26197fa1977b18d881857517dbc1776d16aff1690b1678415ac514ca413aa21306d125d81248711d4c11c151158610ade109cc0fc07085f50772b06a4604d2b0277e0262200e53
|7,1=>0xfd83df2f7bec17ceb769e9bc7e782ae0b3fe0023df27bdec97dd0dadc611d3d7dd18a4ca951c787ec433fba757b8f1fb6f18b6719b2a26abcfaaba56a7f28a5f89a3e07a0d3f
|8,0=>0xfd83df8eb2c1351b5ed4ae2bd6e6716356d528e83c4df3b80c2ac472914228e2826ce319fdc193ea17f2f024f1
|9,0=>0x528e8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0a0a0f0f0a0a0f0f0a0a0000000000000000f0e0f0a000000000f0e0f0af0a0f0a0f0a0f0a0f0a0f0a00000000f0f0f0f0f000f000f0f0f0f0f000f000000f0f00000f0f00000a0a00000a0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0b0b0b0b0a0a0a0a0a0a0a0a5050505050505050500050005000500f0f0f000f0f0f000a0a0a000a0a0a00f0e0f0e0f0e0f0a0f0e0f0e0f0e0f0af0f0a0a0f0f0a0a0f0f0a0a0f0f0a0ae0e0e0e0e0e0e0e0e0e0e0e0e0e0000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e00f000f000f000f0f000f000f000f000050005000500050500050005000500f0f0f000f0f0f000f0f0f0000000000f0f0f0a0f0f0f0a0f0f0f0a0f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0af0f0f0f0a0a0a0a0f000f000a000a00c0c0c0c0c0c00000c0c0c0c0c0c0000f0f0f0f0f0f00000f0f0f0f0f0f0000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f00000000e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0af0f0f000f0f0f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f000f000f000f00
|0,1=>0xe0e0e0e0f0f0f0f0e0e0e0e0e0e0e0e005000000050000000500000f0f0000f0f0f0f00000f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f05000f0f05000f0f05000f0f0500c0f00000c0f00000c0e00000c0e00000000f0f00000f0f00000e0e00000e0ef0f00000f0f0f0a0000000000000000f0f0f0f0f0f0f0f000000000e0e0e0ef000f000a000f000f000f000a000a00f0c0f0c0f0d0f0d0c0c0c0c0c0c0c0c0000000000000000f0f0a0a0f0f0a0a0000000000000000f000f000f000f000000000000000000f0f0f0a0f0f0f0af0f0f0f0f0f0f0f0f0f0f0f0f000f00e0e0e0e0e0a0e0a0e0e0e0e0e0e0e0ef0f0f0a0f0f0f0a00000000000000003030101030301010303010103030000f0f0f0f000000000f0e0f0e00000000000000c0000000c0404040c0404040ce0e0e0e0a0a0a0a0e0e0e0e0e0e0e0e3030303000000000303030303030202f0f0f0f050505050f0f0f0f05000500f000f000f000f00000000000000000000f000f000f000f000f000f000f000af0f0f0a0f0f0f0a0f0f0f0a0f0f0f0ae0e0e0e0e0e0e000e0e0e0e0e0e0e00f0f0f0f0f0f0f0f0f0f00000f0f000030303030303030302020202020202020000000050505050000000005000500f0e0f0e0f0e0f0e0e0e0e0e0e0e0e0e00000000f000f0e000000000f000f0e
|0,2=>0xc0c0c0c0c0d0c0d0c0c0c0c0c0c0c0c00e000e000000000f0f0f0f0000000000f000f000f000f00000000000000003030303030303030303030303030300c0c0c0c0c0c0c0c0c0c00040c0c0004a0a0a0a0a0a0a0a0a0e0a0e0a0e0a0ef0a0f0a0f0a0f0a0000000000000000000000e0000000e0000000e0000000e00000000f0f0f00000000000f0f0f00f0f0f0f0f0f0f0f0f000a000f000a00f0f0f0a0f0f0f0a0f0f00000f0f0000f000f000f000f000f0f0f0a0f0f0f0af0f00000f0f0000000000000e0e00001010101010101010101010101010000f0f0f0f0f0f0f0f00000e0e00000e0e0000f0f00000f0f0000000000000000f0f0f0e0f0f0f0e000000000000000000c000c000800080c0c0c0c0c0c0c0c0000f0000000f0000000f0000000f00c0c0c0c0c0c0f0e0c0c0c0c0c0c0f0e00e000e000e000a000e000e000e000a000000000000e0e0000000000000e0ea0a0a0a0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0a0f0a0f0a0f0af0a0f0a0f0a0f0a0a0a0a0a0a0a0a0a0000f0a00000f0a00000f0a00000f0af000f000f000f000f000f000f000a00f0f00000f0f0e0e0f0f00000f0f0e0e0000f0f00000f0f00000f0e00000f0ef0f00000f0f00000f0f0f000f0f0f00f0f0a0a0f0f0a0a0f000a000f000a00f0f0f0f0f0f0f0f00000f0000000f00
|0,3=>0xf0f0f0f010101010000000000000000f0f0f0f0f0f0f000f0f0f0f0f0f0f000000000000000000f0f0a0a0f0f0f0a0000c0f00000c0f00000c0e00000c0e00000000f0f0f0f000000000f000f00b0b0b0b0b0b0b0a0b0b0b0b0b0b0b0a00f000a000f000a000f000a000f000af000f000f000f000f000a000f000a00a0f0a0f0a0f0a0f0f0a0f0a0f0a0f0ae0e0e0e0e000e000e0e0e0e0e0e0e0e0000000000000000f0f0f0e0f0f0f0ee0e0e000e0e0e000e0e0e000e0e0e00f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0af000f000f0e0f0e0f000f000f0e0f0e00000000f000f00000000000f000f00f0f0f0f0f0f0f0f000000000f000f003000300030003000300030003000300c0f080a0c0f080a0c0f080a0c0f080a0000f0f00000f0f0000000000000e0ec0c0c0c0c0c0f0f0c0c0c0c0c0c0f0cc0c0c0c0c080c080c0c0c0c0c0c0c0c0000f0f00000f0f00000f0f00000e0ef0e0f0e0f0e0f0e0f0e0f0e0c0c0c0c00f000f000f000f000f000f00000000f0a0b0a0f0a0b0a0f0a0b0a0f0a0b0af0f0f000a0a0a000f0f0f000a0a0a00f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ee0e0e0e0e0e0e0e0e0e0f0e0e0e0f0e50505050505050505050500050505005050505050505050000050000000500303030303030303030303030303020200f000f000f000f000f000f000a000a
|0,4=>0xf0000000f0000050f0000050f0000f000f0f0f000f0f0f000f000f000f00f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e000000005050505000000000000000000000000f0e0f0e000000000f0e0f0e00f000f000a000a000f000f000a000a00f000f000f000f000f000a000f000af0f0f0f000f000f0000000000000000f0f0f0f000000000f0f0f0f0f0f0f005050505050505050505050500000000f0f05050f0f05050f0f05050f0f0000d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0000f0f0f000f0f000000000f000f000050005000500050f000f000f000f00f0f0f0f0f0f0f000f0f0f0f0a0a0a00c0c0c0c0c0f0c0f0c0c0c0c0c0e0c0ef0f0f0f0f0a0f0a0f0f0f0f0000000000000000000000000000e0e00000e0e3030303000000000303030303030300f0f0f0f0f010f010f0f0f0f00000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000000f0f00000f0f0f0a5050505050505050505050505050500f0f0a0a000f000a0f0f0a0a000f000af0f0f0f0f0f0a0a0f0f0f0f0f0f0a0af0a0f0a0f0a0f0a0b0a0b0a0b0a0b0af0f0f0f0e0e0e0e0f0f0f0f00000000500050505000505050005000500050000000000f0f0a0a000000000f0f0a0a00f000f000f000f0f0a0f0a0f0a0f0a0000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f0e0e0e0e0e0e0a0a
|0,5=>0x50005000500050005000500000000f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0cf0c0f0c0f0c0f0c0e0c0e0c0e0c0e0cf0f000f0f0f000f0f0f000a0f0f000a00000000f0f0f0f0000000000000000000000f0000000f0000000a0000000a00000000f0f0f0f000000000a0a0a0af000f000f000f000f000f000a000a00f000f000f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a3030303030203020303030303020302f0000000f0000000f0005000f00050030303030303030303030300030303003030303030303030000000000000000f030f030f030f030f000f000f000f000000000000000000f0f0f0f0f0f0a0a00000000f0f0f0f000000000f0f0f000000f0f00000f0f00000f0f00000000f0f0f0f0f0f0f0f0b0a0b0a0b0a0b0ac0c0c0c080808080c0c0c0c0c0c0c0cf0a00000f0a00000f0a0f0a0f0a0f0a0000000000f000f00000000000a000a000000000000000000e000e000e000ec0c0c0c0c0c0c0c0f0e0f0e0f0e0f0ef0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c5050505050505050504050405040504f0f0f0f0f050f050f0f0f0f0f000f00f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0000500000005000000050000000500f0f00000f0f00000f0f05000f0f05004040404040404040404040404040404f000f000f000f000a000a000a000a00
|0,6=>0xf0f0f0f0a0a0a0af0f0f0f0a0f0a0f0a0a0a0a0a0a0a0a00f000f000f000f000f000f000f0000e0e0e0e0e0e0e0e0e0e0e0e00000000f0f0f0f0f0f0f0f000000000f0f0a0a30303030303030303030303020202020000000000f000f0000000000000000c0c0c0c0c0f0c0f0c0c0c0c0c0c0c0c3030303030302020303030303030202f000f000f000f000f0f0f0f0f0a0f0a00000000f0f0f0f000000000f0a0f0af0f0b0a0f0f0b0a0f0f0b0a0f0f0b0ae0e000e0e0e000e0e0e000e0e0e000ef0f0f0f0f000f000f0f0f0f0a000a00f0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c5050505050405040505050505040504e0e0e0e000e000e0e0e0e0e000e000ef0f00000f0f0f000f0f00000f0f0f00f000f000f000f000f0e0f0e0f0e0f0e0000000000000000e0e0e0e0e0e0e0e00000000e0e0e0e000000000e0e0e0e5050505050505050000000000000000f0f0f0f050505050f0f0f0f00000000c0c0c0c080808080f0f0f0f0a0a0a0a50505000505050005050500050505000000000000e000e00000000000e000e0000e0e00000e0e00000e0e00000e0ec0c0f0e0c0c0f0e0c0c0f0e0c0c0f0e1010101010101010100010001000100f0f03000f0f03000f0f03000f0f0300f0f0f0f0f0f0f0f0f0f03000f0f0300f0f0f0f00000f0a0f0f0f0f00000f0a
|0,7=>0xc0c0f0f0c0c0f0f0c0c0f0c0c0c0f0cf0f0f0f030303030f0f0f0f000000005050505050505000505050505050500f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e00000000000000000000f0000000f00c0c0c0c0c0c0c0c0c0c000c0c0c000cf0f0e000f0f0e000f0f0e000f0f0e00f0f00000f0f0f0f0f0f00000f0f0f000000f0f00000f0f0000000000000f005000f0f05000f0f0500050005000500a0a0a0a0f0a0f0a0a0a0a0a0f0a0f0aa0a0f0f0a0a0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000050000000500f0001000f0001000f0001000f000100f0f00000f0f00000f0f0e0e0f0f0e0e3030303030303030303030303030000f0f0f0f0f0f0f0f000f000f000a000af0f03030f0f03030f0f03000f0f03003030300030303000303030003030300b0b0b0a0b0b0b0a0b0b0b0a0b0b0b0aa0a0a0a0a0a0a0a0f0f0f0a0f0f0f0af0f0f0f0f0f0f0f00000f0f00000a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f00a0a0a0a0a0a0a0a0f0a0f0a0f0a0f0a00f000f000e000e000f000f000e000ef050f050f050f050f000f000f000f00e0e0e0e0e0e0e0e0000000000000000f000f000f000f0000000500000005005000500050505050500050005000500f030f030f020f020f030f030f020f02f0f0f0f0f0f0f0f00000f0a00000f0a5000500050005000500050005000500
|0,8=>0xf0f0f0f0f0f0f0f0f0f00000f0f0f00a0a0f0a0a0a0f0a0a0a0f0a0a0a0f0ac0c0c0c0d0d0d0d0c0c0c0c0c0c0c0cf0f0f000f0f0f000f0f0a000f0f0a00f0f0f0f000f000a0f0f0f0f000f000a00000000f0f0f0f000000000f0f0a0ae0e0e0e0e0e0e0e0e000e000e000e0000f000f000f000f000a000a000a000af0f0f0f000f000f0f0f0f0f000a000af0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c5050504050505040505050405050504f0f0f0f0a0f0a0f0f0f0f0f0a0a0a0af0a0f0f0f0a0f0f0f0a0f0a0f0a0f0af0f0f0f0f0f0f0f000e000e000e000ef0f0f0f000000000f0f0f0f0e0e0e0e0000f0f00000f0f00000f0000000f00f0f0f0f0a0a0a0a0000000000000000f0f0f0f000000000f0f0f0f0f0f0a0af0f0f0f0f000f000f0f0f0f000000003030303030300000303030303030000b0b0b0b0b0b0a0a0b0b0b0b0b0b0a0ac0c000c0c0c000c0c0c000c0c0c000ce0e0a0e0e0e0a0e0e0e0a0e0e0e0a0ef0f0f0f030303030f0f0f0f02020202f030f030f030f030f030f030f000f000000f0f00000f0f00000300000003000000000000000000f0a0f0a0f0a0f0af0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0000000000500050000000000000000e000e000e000e000e000e000e000e00f0f0f0f0f0f0f0f0e000e000e000e00f050f050f050f050f050f050f000f00
|0,9=>0xf0f0a0a0f0f0a0a000f000a000f000a00f000f000f000f000f000c000f000cf0f0f0f0f0f0f0f0f0f0f0a0f0f0f0ab0a0b0a0b0a0b0a0b0a0b0a0b0a0b0a000000f0000000f0000000f00000000c0c0f0c0c0c0f0c0c0c0f0c0c0c0f0c0000f0f00000f0f00000f0f00000a0af000f000f000f000100010001000100f0f0f0f000f000f0f0f0f0f00000000a0a0f0f0a0a0f0f0a0a0f0f0a0a0a0aa0a0a0a0f0f0f0f0a0a0a0a0f0a0f0a3030303030303000303030303030300c0c080c0c0c080c0c0c080c0c0c080cf0f000f0f0f000f0a0a000a0a0a000af0f0f0f0f0f0f0f0f0f0e0e0f0f0e0e3030303030303030300030003000300b0b0b0b0b0b0b0b0b0a0b0a0b0a0b0a00000000000000000000f0f00000a0af0c0f0c0f0c0f0c0f0c0f0c0f0c0f0cb0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a00f000f000000000f0f0f0f00000000f000f0e0f000f0e0f000f0e0f000f0ee0e0e0e0e0e0e0e000e000e000e000ed0d0d0d0d0d0d0d0d0c0d0c0d0c0d0ca0f0a0f0a0f0a0f0a0a0a0a0a0a0a0a0050005000500050000000000000000f0a0f0a0f0f0f0f0f0a0f0a0f0a0f0a00f000f00000000050f050f00000000000000f0000000a0000000f0000000af030f020f030f020f030f020f030f0200000000f050f05000000000f000f00c0c0d0c0c0c0d0c0c0c0d0c0c0c0d0c
|0,10=>0xf0f0a0a0f0f0f0a0f0f0a0a0f0f0f0a5010501050105010500050005000500a0a0a0a0a0a0a0a0a0a0f0a0a0a0f0ac0f0c0f0c0f0c0f0c0f0c0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f000f0f0f00c0f00000c0f00000c0f00000c0f0000f0f0f0f0f0f0f0f0302030203020302c0c0c0c0c0c0c0c0f0f0e0e0f0f0e0e10f010f010f010f00000000000000000000f0f00000f0f00000f0c00000f0cf000f0f0f000f0f0f000f0f0f000f0000f000f000f000f000e000e000e000ef0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a00005050000050500000505000000000000000000000000f0f0f0c0f0f0f0cf0f00000f0f0f0a0f0f00000f0f0f0af0f0f0f0f0f0f0f0500050005000500f000f0f0f000f0f0f000f0a0f000f0a00e000e000e000e0e0e0e0e0e0e0e0e000000000000000000f000a000f000af0f0f0f030203020f0f0f0f030203020000f0e00000f0e00000f0e00000f0e50505050005000500000000000000000040004000400040c0c0c0c0c0c0c0c00f000e000f000e000f000e000f000e000000000000f0a0000000000000f0a00c000c000c000c0c0c0c0c0c0c0c0ca0e0a0e0a0e0a0e0e0e0e0e0e0e0e0ef0f0f0f0f030f030f0f0f0f0f000f00f0e0f0e000000000f0e0f0e00000000c0f0c0e0c0f0c0e0c0f0c0e0c0f0c0e0000000030303030000000003000300
|0,11=>0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0ca0f0a0f0a0f0a0f0000000000000000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0000000000000000500050005000500f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0ef000a000f000a000f000a000f000a00303020203030202030302020303020200a000a000a000a0a0a0a0a0a0a0a0af0f0f0f0f0a0f0a0f0f0f0f0f0a0f0af0c0f0c0f0c0f0c0c0c0c0c0c0c0c0c0000f0f00000a0a00000f0f00000a0a00e000e000e000e000e000e000e000ef0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ef0f0f000f0f0f000f0f00000f0f0000c0c0c0c000000000c0c0c0c0c0c0c0cf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c3020302030203020302030203020302c0f0c0f0c0f0c0f080a080a080a080ac0c0f0f0c0c0f0f0c0c0e0e0c0c0e0ef0f0f0f0b0b0b0b0f0f0f0f0a0a0a0ac0c00040c0c00040c0c00040c0c0004000000000000f0f0000000000000f003030303030303030302030203020302
|_,_=>0
def stPool : Nat → Nat
|0=>0x48940c090a89014230204c12080308812040004442070183002000404c0c151001814050587c1004030083c04050143a1c0302036090101834080205010030101802010480810000301026030c824081309060120a0a85c00080082404160204c0606068240813000440c150482028090204c24110501c1610000280a060483c080a0700c1a060280c0802018080200
|1=>0x98206e1a050240e04040d80809038181035048100e1300048120a038d066010304c2a0b0400c120a0301c0832020280e0004874080a070681031020240c08038c0120a0201c0c2f0204c1203030600c090401c082e020200e06050b4120803818082c0301012080d0ac0c0403820122a0204c0c08048a41204098a00018050200e090209c120a020980a000401c0806
|2=>0x2282426150302084060404c08440d0181003020081206038201443048280e3403108100a070681601048280e0104104120a0701408400301012080d0fc140603820123e0304c3408020f4080a03068101d03820060c030040e01048301000030280a040487c0c0a02854123c0402426060a8ec12130a8041033048200e06050e80c090401c1439050180e09020e00c04
|3=>0xa81826580404c2a060495c0c08028101202048280e082b004120a031540a09098100c08208241404039506606038242608298180e0904010a4090301c2651280240c07020289e040481c0c082702426042682030080301c120426010261a040186208048100c02258200c150484c940405038000924824140e02804480902028004823824140423014000a0401c1204
|4=>0x3302414050a804000604854480a328240e0404018c809098100c0831824260403020c40a0301c120b17818100704810c20409824101a300280e080581820040301c12082f81014050702462040381826082f010120a0283800060401c36090601c080604820b808038380209060240c0704010b6090503810040b82408080304cb40405038120806824080a238001009
|5=>0x20280007088100e0903020ec090301c080a3a820120a0a818e8040484c10060c01014083983838040404c0c720d024080a038482204050380a09380242604030545e080481c146e00818140704820da07030201204360100c0704820d6060401c120a350100c0704024d20409868100634020120409818ce09020008e21020280e1c0407412040384c24080501c1606
|6=>0x32180c040404d0a1a048101400238441213020200c840404c0c0104a0c1204050000e820304c2a09040f01204098008e0a03824d004408280e09000102006020241002400180807099fc06090202800073b820261503024fc090202824070c028080704818fa090401c0c0a3e010140507024f6080201812073d024140512018f209050200e7800824080a03848ee09
|7=>0x50480e480501c060b0080014070402c0c930481014070024810090a8182674050200e06022440808038181290020280c070423c0c070484c106d048182a0809a381204050003047038100c0804a3408070304c108c0204c340303000140403024108b050180e0902228140403024108904018000902008100a0382c0c880304c340b041400c130400c0887020241013
|8=>0x20280e1202020261a03070120a0401c0c04510240ea10201810810482810070327c0813048681006000241407028100c9e0301c10030203010090301c080a4e818080a048681049040100c07050253604050240e9a04174120a0401c08064c81014070281812980501c0806040252e0605024100702254120a0401c08063c01808090401c1494030200604038081204
|9=>0x52cc100a0481d3404008100e0a032c4120303028080704821600a038100c0804abc0c0709824100457024080a0001c8e04048200e06052b40c040481c34085602414060382008ab0202810070302554090201c100609aa412040301c100a540240808030280ea6020281007048194a09020280c082406010040301c1c0a4d8201213020182aa304810140e040003009
|10=>0x2818127b04828100703011780a03818107b0202c080a028181c095d82414080381808ba030280807040243e040502012b903038120a038540c084081814070a824103c0202810070481570040501c0a09031a01207098100c08408180e1304820083c020280e05048196e090304c0815042d80c080982434044382008060382414b5048281007020196809038100c08
|11=>0x40180e84020280e09648180006020240e0805320080a038200c313d8200c0902008100a0301d8e090582008070481826c60402414076281802080501c128303004120a0301c0832040240c07020298809020200c070530c1207030298408608181405020541203040280c07020258004050180e0804afc120a0301c082f0481c0806040297c04048200e065e8101407
|12=>0x381812d50302808074382006080481814c203b5008090384cba33040240e040304da604050200e06690200809030280ed0040100e090304d9e080501c2a0903338080a0401d2c060e0240e130213410000401c2609030119c09020280e59000201407071c4080b020241407040199a060482810cc020540c080381408090601812080382872060202026cb0d0241404
|13=>0x20280e060e021be040401c26cb031c4080a0481810076f0280e09040100cdd0501c1208340100204050140c0e0480c0c040382410136e020140603898120b048280e04130206606050100e090436c0c0a03868160828024140707004102403010100704829b404038240c086c0241407021181000030101013660243406040240e040d35c080a0481c10066b0101408
|14=>0x3000080a038383808018201204030280eec048280a0607010a009050100c0803bac1204098200c000c01814090381010ea0501c080604821d20905010020803ba008080481c140673824080a038200ce6030101013728243409050100e080339008070480c0c0a538101409040180ee302020120705019c4090501c103403004120a0301c0808708241406038ec1024
|15=>0x381010067d02012070304c08f90501c0c0804811f00a038240c08023dc120a0301c10047b01810130d010160a03820060b0300414070082416080001014080281812f50302810077a02416040384c120604364120a0201c0c087982012070204c0cf203024140704011e2060382410041e3c0120a0382090040081014090381810ef0481c100605011dc040501c3403
|16=>0x40900c040401c1409840100e09040280d070481c0c0a040120c060201c12030519412040301e0a0a820101406038241103048100e0609822020405024100703400120704018080a7f8100c070702014fe0481c26040302080040502410030398012060504c2a0812018120a0285448090501dc00104090100a0201812077e82026040a818121c048100c0704029f809
|17=>0x98206e090384c0c010409010090501c08062c02414060209810050301014078780c0c0a0386808081e0240807098a00006050100e0804c38080a038381208188100e13030221a080484c08060a8981204050180e08240200c090201e1609020280e0e040000c0a0386810045702012040301e12040482810a0070200e13031c4080b040240e1503029840903a840c01
|18=>0x6f8201204030280f150481c2604008200004050240e06044500c09040102a0a118201404038240c880304c121a04010a004050240e1a042e0120a0301c100489820120a098540c01040240e040334c0809050200c050c0240ea1020041000048100e060982224090202800470301014070402622060402426cb02054120a038140c0488010100a038240c72030100e09
|19=>0x38220a04008201204038280d22020281007030264208048100e150348014070202012068f824140403c781000030101207044740c04050240e0839824140803818091c020280eca0481862040501c1003031ec100a0201c0c098d818140803810131a048100e080304e3204050180e08048741204050380a00020281007030262e04050200e09399800c0a038101608
|20=>0x1102408080301c15280201c26090401862040481c260803000080a04aec0c070c024080a030201d27020280c07930240604048200f18051bc0e080300012048601814080386c120b030100e13658200604050180e0804c941207051bc02081201810070484c084402028100703490080750824100618818080a0386810c90402812070301246080501c1c010482c120a
|21=>0x70201249048280e0e040113c090501c1c08021080c090401c080a9881014060401c12290481010060501e5e06050240e04044b81204050a000070c024140603810103204018080704a1dae0a03820a00b031c41207054b4020812024080a038201ce6048100c0e0402a58040384c0c0895820120a038100d2a030240e041202846090201c100609ca4080a0481c0c08
|22=>0x40cc080a03b280c09380101408038240a600202812074e01800090201c100610810140e04014121c020280e0e040256e040384c0c0804cdc0c0a038541608018180e130400c080b0302812080201e6c0405018100903cd4080a0480c0c070c0280e0803278120b03010261a0400c10070201802099a0100e0a968701003040240807034cc120a0401c0c04990101406
|23=>0x482808070401a7e09020280c08238180807048207e0903810100a034f808070480c0c0a98018140702824083c04810260803060120a0301c08089e820120a03cf008010501c080604822760a038240600020040c0a03814120457024100702818093a030241013660102a06050200e09024e414070481810044981012070404c0d38048280e150082066090384c0801
|24=>0x382290090501c2a080310810090201c1406a38241404030040e2f030240e0809811e208050180e09025180807098240c084c02426040a8181033020280eca03024f6090501c0a00021341204040180f440201c100a0481a86040384c1206041c010040301c1c0aa102414070702008fb040180e0e048121808048100e0605504080a0303812086f8100e06040241540
|25=>0x48280807040188208050180e090254008070981810093d82414070453c08010482810050a8180209050200e04035381204038200c13a68241404038200d4c0501c0c1c020207a09050180e04130bc10040301c1409a581014070d0181031038200c00048101808048180e0a02528080a048180e08a48100ea103020127b04018260404a0c1006038240813250240806
|26=>0x48200806aa8101407049cc0c00030100e08098262204048200e0a035500c0a0401c1204a982408080311c42040401c1213031c812040501c10065482012070201826580202414050702000090501c020800440100403024340a520181013048110e060201c340a8200c10090301c08c4040280c0e0d0101606050100e0804d481207020181408a881826040a8241003
|27=>0x1002060481c0824051941208038140c0aad018080a0382410dc0482808060401cc609020180e0a0456412060201c100aac02408070702014b1048100e0609822ae04050240e1a0418010060201c12d704828080703020ac08020180e0aa102012070a828de010481c100605012ac09020280e0009020080a038240cc602024140507018ba0a038100c7e0400c1407
|28=>0x3808080a0301c108f040240c07025880c070482008f0048280a040a818000a0381810090258412040301c100ab00201404038240d5f048200e05030121409020285000039200809040280c07af024140803ad80c01048100e08035340c0a0381408091e810140903a580c000482808080301eba0403824100605570120a038380808ad81014070312012bb048280e05
|29=>0x201c15040480c1009050180e04230240c0a0201c1034040181404038250e040501c0c08958201207098100c4d0302808070a82012030202410070302aca0902028260803060080803868380a96824080a038200d19048280c071302048090204c10062381812080381015640201c100a7f018380a038241004030400c0403824060a118180809038201563040181204
|30=>0x382198060482810070206c120a0301c1c08021401009050180e041d82414070401ad2090501c0801040cc0c04038241168040100c070702415670402408060382acc09020280c070403890080501c080600824fc040501c0c0804cdc0c040501c26090400c0c040501c0a090181814070400c080b040240e04030041516040101407070243804050180e0e040240606
|31=>0x38200c000256c0c0a0481c34040409010090201c0c13b582012060504c081502024140702818100004024140770010020404828100703398080a038240c08380240c0a038541024030240e13020204806050200e05020241606020281207042700c04040240e1a055a80c0903a84080812018080903868100a59018120a038140850048280e0803000091003010120a
|32=>0x39824080704018000a53824080a040180ee8020280e0604024f609030100e150402a08040501c1208031a0080a0382410065b820120a038540c01040240e13020180208048100e150302a5a060201c100a04bf8080a0481c340604174080704029640604870100903a84080600824140603b80100428010120709818105d03020140903812d8040501c120604260120a
|33=>0x4810140603820b204048280e05030206606020281007049cc08090501d94060002012070201a74040402812070306adc09020180e0e0402a08090202810060391c120a0381010067d8180807052c812030301010070484d96080501c08060495c1204050180e0824024080a0383810000501c0808120240c1c048100e08035b41009050100c078f018080a048200607
|34=>0xb3824080a038381033048101406038220a080482808070a8194606020280e05048200604050240e1a0302000080201c2609031c410090201c0c1381018080704029fc090201c2608030001009030100e0ab80200c0a03854120b040180e13048101609020281006b781808080982434090201d42080300010040382a5a090e0100e06054b41009018180809040280f2c
|35=>0x2028100623824140702018115b030101408038240a73020280e095d81800060482810050205412040384c1006140241407020040c0800010140803b280c090e02012060201c1572020240e080501962080481c0806053b41009050100e06b88280e040409012063882408070401a8a0602028120803a580c08050240e040d21c1009050100e063c818080803814120a
|36=>0x328280e0803000120405820120a0201c2a0613024080a0301c100e930181207020201574030241407098101024048100e08030001530048280c07070200824040280e0403024fc080481c0c0aad0201207020181516020280e090181800090201c10060529c1204050181c0802810120a0401c0d73048101408030000e18030280e08280241609020180e0e040296409
|37=>0x50200c070c02414070300410240481c0c0a9682008240481014071400012040501c2608030000c04048200e0505194120a0401c0a06021341004050240c077a8240e04055d81006000280e090400c080600824080a038ccba08020280c070483adc080501c120602338100603824090c04810140603822ea06050240e1a02020a006048281007022d80c04048200e0a
|38=>0x20280c0770018080a038241003048101407040186606020280e09042ec1009020181407098201204050180e0e048101407040185008048180e04055d810090302808070a820080a038240c7104810140704018000a038240c7104010a0090201c1006054c0100603824080c048101408030000e48020280e090400c0c3103010100a038259608048280e0e021341204
|39=>0x8048100c0a03824080a038200c00040181407048101606048280e04040901009020180e1304024080603a8410090201c0c0a96820120403818146f0402408060501c1009
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0xdaa0685031a817940b2a0545027a8129408aa040501da80d94062a02c5013a8089403aa0185009a80394012a0045
|5,0=>0xf53079543bec1d960e9b0735838ec1c160ddb06d5835ec1a960d1b0675832ec19160c5b061582fec17960b9b05b942d0c16260ae3055982a0c14a60a2304f98270c1326096304998240c11a608a304398210c102607e303d981e0c0ea60723037981b0c0d26066303198180c0ba605a302b98150c0a2604e302598120c08a6042301f980f0c0726
|5,1=>0x1b330d8186b4c35551a7b0d258686c33d619bb0cc58656c325618fb0c658626c30d6183b0c0585f6c2f56177b0ba585c6c2dd616bb0b458596c2c5615fb0ae58566c2ad6153b0a858536c295614828a29850aa27f613cb09cd84dac2676130b096d84aac24f6124b090d847ac2376118b08ad844ac21f610cb084d841ac2076101287f183ecc1f06
|5,2=>0x804c3fc61fb30fc187d4c3e461ef30f6187a4c3cc61e330f018774c3b461d730ea18744c39c61cb30e418714c38461bf30de186e4c36c6
|6,0=>0x2dcb96c9cb56e5a472ceb9659cb20c58972c1b15f1caeae56e72b3b9581cab2e55272a5b9511ca7ae5367297b94a1ca42e51a7289b9431ca0ae4fe727bb93c1c9d2e4e2726db9355899ce4c77260392e5c964e4ab725239275c92ce48f724439205c8f8a4766237b91a1c8c4c45b722a39139888ee440721cb90c9c856e424720eb9059c81ee4087
|6,1=>0x3b839da5cec4e75b73aa39d35ce8ce73f739c39cc5ce54e723738e39c55ce1ce707738039be5cde4e6eb737239b75cdace6cf736439b05cd74e6b3735639a95cd3ec6987348b9a29cd06e67c733ab99b9ccd0c661732db1951cc9ae646731fb98e1cc62e62b631239875cc2ce60f7304b180d8bf8e5f572f73979dcbc4a5db72ea39735cb8ce5c06
|6,2=>0x492ba4815232e9127485ba411d1fae8f67477ba3a1d1c4c8db746ab2339d18ee8c1645d3a2cdd15ac8a6744fba2659126c88c7442ba1f9d0eee8707434ba189d0b6e8547426ba119d07ee8387418ba0a9d046e81d640b3a03dd010e80173fdb1fd1cfdae7e673efb9f658fa4e7cb73e239ef5cf6ce7af73d439e85cf34e79373c639e15cefce7777
|6,3=>0x5703ab65d5a4eacb75623aaf5d56ceaaf75543aa85d536ca947546baa19d4feea787538ba9a9d4c6ea5c752aba939d48eea40751cba8c9d456ea24750f3285dd420ea0975013a7edd3e8e9ed74f33a77dd3b0e9d264e5ba711d37ae9b674d7ba6a1d342e99a74ca32635d30ce97f74bc3a5c5d2d4e96374ae3a555d29ce94774a03a4e99266e92c7
|6,4=>0x64bbb241d914cc83763eb31d9d8deec687630bb169d8a6ec4c7622bb0f9d870cc3176153b08dd838ec1576073b01dd800ebf975f9b2fb597ccebdf75ec3af499796ebc475debaed9d75eeba875d0bae69d726eb8c75c2badf9d6eeeb7075b4bad8d96b8eb5575a73ad1dd680eb3975993acadd648eb1e658bbac41d614cb03757e3abd5d5dceae77
|6,5=>0x7283b925dc84ee3b771a3b8b99c4eee20770cbb849dc16ee0476febb7d9dbdeede876f0bb769dba6edcc76e2bb6f9db70cdb176d5b3691db3aed9766c83b625db04ed7b76ba3b5b5dacced5f76acb3549da96ed44769ebb4d9da5eed2966913b4719a2aed0e7683bb401d9f2ecf27675bb391d9baecd67667bb321d982ecba7659bb2b1d94aec9e7
|6,6=>0x1d92eec2775dbbad1dd5aeea767503ba65dd24ee8b77423b9f99cf0ce72673633995dcbcee577
|7,0=>0x84e3c252211cd087783fc41de20e0f0697830c4169e0a6f04c7822bc0f6206cf02e88134407de02f10107804bc009dff50ff287f5bbf91dfb90fd577e73bf1ddf80efb977d8c3ea9df450f9b77c9c3e31df090f7d77bb3bdba1eceef6167ad3bd519e990f45779ec3cd61e5cef26878fbbc61de210f097780c3be9dde6eeec7772bbb7d9db0eed08
|7,1=>0x933c4981e4b11250892444905e476d2347916bc899e43ef218790844825e40311fb68fa3c7b223caf1de78ebbc73e238f11c078dcbc6c9e356f1a388ceb4659e31d118778bfc45e1e2e2f16988b0c456622a4f14b78a2b44f9e26ef1307894bc48da23ad1167887bc41e2200f0f97878c43a9e1c6f0dd686ac4336218cf0bf785c3c2c5e154f0a37
|7,2=>0x99abccb6264cf320698c44c422612f302797dbcbd1e5d912e6696f44b5a259d12c7795fc4ade2562d2a989513ca71a52af28d89433c9fde4ef126f8
|8,0=>0x2760f3a979d13ce71a72cd38f79c43ce09a6f6f37479b6bcd99e6bef35879a8bcd29e686f33c7
|9,0=>0x13b76
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 375 then fld (dictB (i / 512) (i / 32 % 16)) 124 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 9 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 17 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x5828048110584e020250201d0501d02021020190401d0301d1401d0001d04019040180601d05828048110482102019020250481d0301d0700c048210481d0301d01854040250201d0401d12025040110201d0401d000a304019040180501d04821020250201d0501d0700c04025040190301d0e021030250481d0301d040190401d020390301d030090601d0582802025020190601d0582804811048210401d
|1=>0x401d0301d030110a9bf0302b0201d238291401d04019040180183804025048190301d000a304019040180501d02829040110201d0401d00025030210301d0401d03175030220301d0401d0582802025020190301d00814020190401d0301d00068030210481d0301d040192c81d040380301d00827030110201d0501d0601d05828020250401d00054030210201d0501d01819040250481d0501d0300a0601d
|2=>0x4811048210084c030110201d0501d0601d05828048110401904013048110481d0501d0d011040250481d0501d0011f1401d0401904018240a30001d04019040181401d04019040180501d040090601d058280202503849000a3040190401800825030110201d0501d03849000a304019040180384a000a304019040180084c020190201d0501d030250301d048150401d0384a000a30401904018041c50481a
|3=>0x4018029bd0302b0401d052730d0220481d0004e040190501d5381f00029040192401f040390301d52027070290301d030570201d0501d0001f040190301d000a30401904018048190481d0501d02283030140401d040190481d0501d03141020220401d05828048110482113029020390301d03a710d0220481d041c7030270401d04a050082302019022590181f048210601d0582804811048210401902019
|4=>0x204e0501d03011048560201d13023020390301d61021021bd0302b040250201d0401d049190203a0301d13020020390301d50029030140401d04811000270302101854040250201d0301d048160401d04006020190201d0402d048110201d39818048150401d0181b048210401d0200d048210501d0a8210201d0501d0d0110481d0501d030110306a0481d04025032c90402b0200e048210501d1401d04019
|5=>0x481d0404e0501d4382b020690481d04025048550201d6101d021bd0302b0401a030220501d099370201a0501d04a81030140401d6881f0e02904819099c70481a0501d021c50481a0201d048190181f0482104019040380301d0201d0404e0501d05828020250401d32813028290401d0481d0484e0501d0302104b290401f0d2cb0402b0481d1882701819048210601d0582804811020250081f0201903011
|6=>0x482102019040390301d03bb50082b02019020220301d0401d03a0500823020190001f040190501d041f90082502019038cd03023020190481d0404c0501d030d3040560201d00029040190482102019040560201d04011023810301f0481a0484e0501d020190181b048210184c048210501d02025020390301d03023020390301d0420d048560201d02022020250481d02021020190301d053650e02204819
|7=>0x302b0201d04011020190501f02829048210401d040290403a0301d044090304c0501d04ac90402b0301d041350201a0501d3981b0181d04821040110201d0501d040110201d0401d04011020190301f3f01f0082502019030250201d0501d053ef1201a02021021ed0002703021048110481d0501d020190481104821030210202502019039c5030270401d020250394102022033170204e0501d1e02b01811
|8=>0x4b310404e0501d0201d0484e0501d00013030210401d0332d0484e0501d0432d0484e0501d04011020190501d0084e020190501d0401d020390301d048210d0200481d05821020250481d04019040180501d048d1040560201d04071048190301d048a1030200501d030550201d0501d03c310582b04811040cd0401a0301d0200e048210481d8501d051370201a0301d030140401d048110481a0501d021bd
|9=>0x401d04a710d0220481d02025020190301d020190403a0301d0528d0a81a0201d052710d0220481d1882701819048210004c040190501d01838040250301d040190401d0301d04c61030160401d3981b048150401d0d023020250481d8b01f008290201904019020190501d040130481d0501d031cc0d0210481d020190201d0501d099370201a0501d2401f030150401d04019020190501f1401d0401904018
|10=>0x30130401d03aed040270301d03141040130301d020cd0401a0301d03cc10002b040190001f04019040184382b048550201d020210201903029034990403b0301d03ac90402b0301d048a3030200501d033150204e0501d0300d048210501d03175030220501d03c990403b0301d048210403b0301d0582b048110401904811020160401d040250484e0501d02021020190302b0232d0484e0501d04a8303014
|11=>0x3011039bd0302b0080e048210201902019040190482101813048210401d05135030130401d0201d0404e0501d033330404e0501d0401a020190201d0401a020190501d3981b048150401d1404d040180501d048190401d0301d032ed040270301d04025048110201d02025048210501d0001f0401904821020250314102022040250481d0501d3f02b00825020190402504819030290528f0a81a0201d02937
|12=>0x481d05828048110401952013070290301d0a8270201d0501d0584e048110501d2c82a040380301d020cd0401a0201d130200081d020190702f048110301d030230201d0501d03d151402a04018041c50481a0501d52024070290301d0582b048110301d051e50a81b0201d0d0230481d0301d0a8cf0401a0201d2c81d040380301d09aed048220501d0002b040190482101811048210401d0001f040190501d
|13=>0x18130482104019048150401d04b310404e0501d39811048150401d238291401d040180332d0484e0501d0004e040190501d030210301d0401d000130302102019070290481d0301d0d0110481d0501d04821040290481d051190203a0301d020250481d0301d01857040250201d048210201d0501d00054040190201d00027030210501d03011043810301f1404e040180501d0494102022048190e02103025
|14=>0x511b0203a0301d021ee000270302105137030130401d0001d04019040181404e040180501d04941020220401d040190181f0482103bed1201a0202100821020190301d02829020210401d021bf0302b0401d0184c048210501d032c90402b0301d031ce0d0210481d4382b048550201d52024070290301d030110302b0201d000a304019040180e04e048190501d030220301d0401d040250082502019032b9
|15=>0x497503022048210501d048210401d04811048210082902019048190301d040250301d04821040290203a0301d040560201d048550201d048a3030200201a0501d040250201d0001f040190501d03029030250481d0004c040190501d02021020390301d1401d040180501d0506d020160401d0481904ac90402b0180402019048210282b048210401d0d2c90402b0481d0601d058280481104965040380301d
|16=>0x40130301f030220501d0206a0481d041c70481a0001104019020210481d0304e0501d0201d0501d030210401d020190301f033290401f041c50481a040110201d020210501d020250401d0d0220481d0d0290481d020210501f0402b0481d020220401d00013040190404e0501d020160401d040130301d023810301f020a1040180302302019052ef04822048290301d0702b0301d040390301d0082502019
|17=>0x3ac90402b040380301d030230401d048150401d030210401f051350201a030690481d040290301d1401d040181201a02021048210402b0484e0501d0082702019040390301d040190301d04819020211402904018039350201a0181d048210002904019038cd0401a0002703021040290201d0181b04821032ed04822020190201d020190501d030290201d04ac90402b030220481d030250402b020190501f
|18=>0x4019048220201d0401d040180501d0302102019030250401f0a8290201d032c90402b0082b020190a8180201d0481a020211402a040180181f04821020690481d0a81b0201d048290401d0401a0301d0403a0301d0a81a0201d048210401d030210481d0481a0501d0304c0501d04ac90402b040190501d0a82b0201d048110201d048110501d1401e040180481d0501d040190501f04819030290402503029
|19=>0x30130401d039c50481a040190202902019048210401b0401a048390301d021c50481a0582b04811043830301f020220481d020150401d028290401d04811040190a8190201d0403b0301d1202902021020210501d0002b04019040110301d0082502019021bf0302b0082902019040190482100029040190401d0301d030170401d0001f0401902025020220402b0301d1401d040180082102019048150401d
|20=>0x401904811020210501d0501f030290302b0301f048210401a048220501d0301d04018020290201d0481a04019040130481a0002b0401905828048110001d0401901819048210484e0501d0201a0301d0001f04019020210201904011030290401904018040190501d028290401d
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x55000000000000000000000000000005
|5,0=>0x232000000000000000000000000000000042407c80e90000036406480000000000000000b900000000054800000000000000000001320000000008900f200000000000000000000000000000001a400000590000012401c800000000000000000000000000000000000000000014800000000000
|5,1=>0x29900000a24000000004f20000134825900000000000000000000000000024904720000000022900000864000020903f200000f48000000000000000000000000000ec81c90372000000001a9000000000000000000000000000000033200000c48000000005e40000169000005640a48000027204a4
|5,2=>0x612000017c800000000ba400000000000000000000000000000000000000000000016c800005920ae4000000005520000
|6,0=>0x9a9932325e60000961800025260000000126300000000919920323a6468c8b991430000444c00010e32166000000000002106414c000000020463fcc7e18f93000000007b180001e6600007818ed31d4639cc7218e13000000006f18db31b06354c6918cf3000000000000cc31926318c0000000
|6,1=>0x37266d8cd999b0300006b4cd518000000069ccd219a1300000000cf1800033660000cc180000000654c000192331e6630cc49986330660000c0180002fa65e8c00000002ee65d0cb8996e32d665a0cb2996232be6000000015c300000000ac995632a66540c00014d3294651cca21941300004f8c9d99383
|6,2=>0x900d1e9a3a346e68d0d189a2e345668a0d129a22343e6870d0c9a16342660001081a0d3414681cd021a0133fc67ecc000000000007e0cfa980003e4600000001ef33d867a4cf319e333c06774ced180003ae60000ea180000000744ce719cb33906714c000000038460000df99bc3000000000000000
|6,3=>0xac8c0002af30000ab0c0002a9354c6a8cd501a9d30000000000000005346a5cc000294352260001471a8b351060001429a8234fe600013e180004f269d8c00000004e66000000027030000000000026d300000001351a6734c86984d2f1a5b34b06954c00000000000948d27980004986924d231a433
|6,4=>0x19b1b3336606cb4c00032a30000c9cc000324300000001909800063c6c6cc000318362a6c48c00030f36186c24c00030636066c00c0002fd35f46bdcd7a1af135dc600000002eb35d06b94c0002e230000b7cd6e1ad930000b58d69980000000b40d669aca358e6b10d609abe35766ae0d5a98000
|6,5=>0xedcdda180000000ec4dd71bab375060001d2980000000e88dcf9b9c30000000000039930000e58dc9980007206e34c00038a370e6e10dc09b7e36f66de0c00037536e46dbcdb6180006d26d98db19b6036ba6d68dab9b5430000d44da7180006966d20c000000068a60001a1180000000cfcd9e1b393
|6,6=>0x3e137bc6f6cdec1bd537a46f3cde61bc9378c6f0cde01bbd300000001dd18000
|7,0=>0x8c45180a2f145c28b45160a2b145428a45140a27144c28945120a23144428845100a1f143c287450e0a1b1434286450c0a17142c285450a0a13142428445080a0f141c28345060a0b141428245040a07140c28145020a031404280450009ff13fc27f44fe09fb13f427e44fc09f713ec27d44fa09f313e42
|7,1=>0x9c45380a6f14dc29b45360a6b14d429a45340a6714cc29945320a6314c429845300a5f14bc297452e0a5b14b4296452c0a5714ac295452a0a5314a429445280a4f149c29345260a4b149429245240a47148c29145220a43148429045200a3f147c28f451e0a3b147428e451c0a37146c28d451a0a3314642
|7,2=>0xa343460a8b15142a245440a87150c2a145420a8315042a045400a7f14fc29f453e0a7b14f429e453c0a7714ec29d453a0a7314e42
|8,0=>0x2958d2a1a5234a06938d261a4a34942920d231a4434846900d1f1a3c347468e0d1b1
|9,0=>0x52c0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 20 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 511), wireSAt ((code >>> 11) &&& 511)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 15 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|4,0=>0x8000000000000000000000000000000000000000004
|5,0=>0x4000000002300000000000008080000000000800020000000000000000000000000000000000000000004000020000000000000040000000080000000000004000020000000008000000000000000000000000000000000000002c010020000300600000000000000100000000000000000000000000000000000000000000000200000000108000000000000008000000000040000000801020000000000001800004000000000000000200000000000000000000000000000000000000000000001000402000000000001000000008000000000000000000000010300000000000400000000000000000000000000000000000200000000000000040000a00000000000000000000000000000000000000000000001000002000000000000800000008000000000000000000000000000000000000000000000000000000000008000000000000000000
|5,1=>0x80000000400060000000000000014000000000000000000000000000000000000000000000000000000000000000000400000010001080000000000000000000200000
|6,0=>0x88001000000200001000002000000000800000000000000600000a000080000000000010000000000081000000000020000000000000001000000000180000400400000008800080080000000000800000000100c200000000000000040800000044030c600014000548000440003000001004000000000000000041000000000000002a0000500000808064000000080000008c0202000918000080000000024001000000010000000000000800000040000200000002002000000000080000000000000040000000000002002008000000080400400002000010000000001000000210004c0020000000000000000000020000200000000000000020162840000400001000000000000000200000000088000004800200001040000000840311e10810000000000000000200800000008010390000000041000000000000000000001400002000000000000000
|6,1=>0x440000000001000002000080000000090000208003400201680000000000000000000000000000008000840000000041000040000000100000008000090000000200000101000008000000008200000400000000100000000000000008000000000000001000000000000000100008000000000000000600809120308000200100000004000088040100000000000000000000300000200000000090020d4400020040400000016200000040200800000800240008020100000000804002000820000500c11a0000000002018230600000000000022000410000200309c0904280004000088012000000000000000002000200000400000002008000000000000001000008000200202001045000102000000001800000000110000000001000000000002400400300081000020100000200000000000000088000000000c00004000000000000000000000
|6,2=>0x400002000000000000600c00002008000004000000000002000000000000001000002000190000000000000000000410000000000400002000004000f00004000000018ad00000800085030000000400400000020000008000000c01000244000060000000020800010000109800c0020900000501000000080000000003002002000000000080001000000000000000180000001080000000000000000400100000040000000000010410800000000180000400000000040000020000000000010040000000000003006000000000080000400000000010000200200000000000200203000406400000000080000280000800000000140000400003000002000010100a000000000000200000010000010000000000100000006044010000000100000004001020080000000000000020000101001f000020002400004200004004200000040000200000
|6,3=>0x20004800000402000018020000100020003000000080000800123c0880a00083000000000010000000000
|7,0=>0x2020a0066c0202e0009200802b060240187e8041b8043700127c48002008a500030a00100001a2018ce20805cc0024038802904500c3990419001092804980085fa0104c0314a0102c00c31c0201d300080900a001098121800801c08021900240020000007e008358086d8001fd009268900140c0a80239c2103e004cd4005d000268421360546910030cc203c0a0820189f0a41000104c0b19a018a10092e00a079820122400f02030806030031aa05887980048012480914e0086f00209c0201c0385a4802f0081f80024e021b6008480040d2012a4000ca0107b48c020043a4820080100d0101ea00044400c24088100a178002b41208a0105f4080000712404424810cf0000d021114020880209f1000700011483112018c920c5400432c004260049f12020b02022038d20001b90027e06110003240480100404a011680a01c0900a4cc048043a40306e0100c
|7,1=>0x378001b00093e0048f12000c0200104926048a4000379040b80012c018a100048809048020420408f000c8006030031c21480820846a0601c031c20004c1480780127d010084c021
|8,0=>0x39ce818054082780007d0091e8049f0060b8001bc0114b81c4f00c728071250093e048af00c70a0166d1201e000ad
|9,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 21 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_122,7,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 1 then [(dom_121,7,runOps true dom_121 (0,roots_121) ops)] else [])++(if pm.testBit 2 then [(dom_107,7,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 3 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 4 then [(dzo_121_2,6,runOps true dzo_121_2 (0,roots_121) ops)] else [])++(if pm.testBit 5 then [(dom_115,6,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 6 then [(dom_59,6,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 7 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 8 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 9 then [(dom_89,5,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 10 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 11 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 12 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 13 then [(dom_120,4,runOps true dom_120 (0,roots_120) ops)] else [])++(if pm.testBit 14 then [(dom_114,4,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 15 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 16 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 17 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])++(if pm.testBit 18 then [(dom_99,4,runOps true dom_99 (0,roots_99) ops)] else [])++(if pm.testBit 19 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])++(if pm.testBit 20 then [(dom_27,4,runOps true dom_27 (0,roots_27) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_123 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_122 _ g hchk
    · exact cpcs (by decide +kernel) low_121 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) low_91 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_121_2_48 _ g hchk
    · exact cpcs (by decide +kernel) low_115 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
    · exact cpcs (by decide +kernel) low_113 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_89 _ g hchk
    · exact cpcs (by decide +kernel) low_57 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
    · exact cpcs (by decide +kernel) low_43 _ g hchk
    · exact cpcs (by decide +kernel) low_120 _ g hchk
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_90 _ g hchk
    · exact cpcs (by decide +kernel) low_58 _ g hchk
    · exact cpcs (by decide +kernel) low_99 _ g hchk
    · exact cpcs (by decide +kernel) low_73 _ g hchk
    · exact cpcs (by decide +kernel) low_27 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_122 7 s (0, roots_122) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_123 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_122 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_123 == dom_123) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_123 goalM v ys) : RunD true dom_123 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_123 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_12 : ∀ i, 12 ≤ i → i < 22 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 12 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 22 → Z 4 i = true := (range_split z4_0 z4_12)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_144 : ∀ i, 144 ≤ i → i < 154 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 144 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 154 → Z 5 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z5_0 z5_12) z5_24) z5_36) z5_48) z5_60) z5_72) z5_84) z5_96) z5_108) z5_120) z5_132) z5_144)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_396 : ∀ i, 396 ≤ i → i < 402 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 396 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 402 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108) z6_120) z6_132) z6_144) z6_156) z6_168) z6_180) z6_192) z6_204) z6_216) z6_228) z6_240) z6_252) z6_264) z6_276) z6_288) z6_300) z6_312) z6_324) z6_336) z6_348) z6_360) z6_372) z6_384) z6_396)
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
private theorem z7 : ∀ i, 0 ≤ i → i < 156 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72) z7_84) z7_96) z7_108) z7_120) z7_132) z7_144)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_12 : ∀ i, 12 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 12 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := (range_split z8_0 z8_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_123 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_123 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_123 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_123 roots_123 goal_123 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_123

theorem low_123 : Lower true dom_123 roots_123 goal_123 10 := S_123.noCircuit

theorem low_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_slice (d:=dom_210) (dSub:=dom_146) (T:=goal_210) (TSub:=goal_146) (roots:=roots_210) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000000000000000000000000000500050000000000000000, 16, 80)] (by decide +kernel) (by decide +kernel) low_146

theorem low_242 : Lower true dom_242 roots_242 goal_242 6 :=
  lower_slice (d:=dom_242) (dSub:=dom_210) (T:=goal_242) (TSub:=goal_210) (roots:=roots_242) (rootsSub:=roots_210)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5000500000000000500050000000000050005000000000005000500000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_210

theorem low_218 : Lower true dom_218 roots_218 goal_218 6 :=
  lower_slice (d:=dom_218) (dSub:=dom_210) (T:=goal_218) (TSub:=goal_210) (roots:=roots_218) (rootsSub:=roots_210)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5000500000000000500050000000000050005000000000005000500, 64, 72)] (by decide +kernel) (by decide +kernel) low_210

theorem low_248 : Lower true dom_248 roots_248 goal_248 5 :=
  lower_slice (d:=dom_248) (dSub:=dom_184) (T:=goal_248) (TSub:=goal_184) (roots:=roots_248) (rootsSub:=roots_184)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x101010101010101000000000000000001010101010101010000000000000000, 8, 72)] (by decide +kernel) (by decide +kernel) low_184

namespace S_202
def pairsG : List (Nat × Nat) := [(2,130), (8,72), (8,136), (10,74), (10,138), (64,72), (66,74), (66,194), (128,130), (128,136), (192,194), (192,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_202.map (· &&& dom_202)
def goalM : Nat := goal_202 &&& dom_202
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x5080f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a0000000000000a0a0000000000000000000000000000000141400000000000000000000000000001414000000000000000280000000000000028000000000000002800000000000000280404000000000000040400000000000004040000000000000404
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 203 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 5 (j % 64)
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_202 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_202 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_202 == dom_202) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_202 goalM v ys) : RunD true dom_202 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_202 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_202 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_202 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_202 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_202 roots_202 goal_202 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_202

theorem low_202 : Lower true dom_202 roots_202 goal_202 4 := S_202.noCircuit

theorem low_234 : Lower true dom_234 roots_234 goal_234 5 :=
  lower_slice (d:=dom_234) (dSub:=dom_202) (T:=goal_234) (TSub:=goal_202) (roots:=roots_234) (rootsSub:=roots_202)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50500000000000005050000000000000505000000000000050500000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_202

namespace S_250
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,130), (8,40), (8,72), (8,136), (10,26), (10,42), (10,74), (10,138), (16,18), (16,80), (16,144), (24,26), (24,56), (24,88), (24,152), (32,34), (32,40), (48,50), (48,56), (48,112), (48,176), (64,72), (64,80), (66,74), (66,82), (66,98), (66,194), (96,98), (96,104), (96,112), (128,130), (128,136), (128,144), (160,162), (160,168), (160,176), (192,194), (192,200), (192,208), (224,226), (224,232), (224,240)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_250.map (· &&& dom_250)
def goalM : Nat := goal_250 &&& dom_250
def NN : Nat → Nat
|4=>0x5
|5=>0x10
|6=>0x24
|7=>0x9
|8=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x90f4380c1462044295291c274
|5,0=>0xf7247d49d3c39dbb55dd96b479321791b136c9d54c2ce492684309941f6c27f5d1cff71aca80ccc8
|6,0=>0xe9feddcb7eda517d929fd49d3c79b8c3931c0076ba472aa143a52689d3337e0c27cfe57441d6fd3061bfb5ea6a5bad25b4b952a58524c74fa5848d043dabc38a5333a7130a962d79a2be38292b022bfb1f08a13072043c8000fc
|7,0=>0xc00768dadb69d9c4ccce3c66038a4b2cb2b0909902108
|8,0=>0xf38e2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a00010141010101410101014101010141010101410101014101010141010101410128002820280028202800282028002820280028202800282028002820280028250505050000040405050505000004040505050500000404050505050000040400000000a080a08000000000a080a08000000000a080a08000000000a080a080000000000000001010101010101010000000000000000010101010101010128002800280028002820282028202820280028002800280028202820282028250405000504050005040500050405000504050005040500050405000504050020208080202080802020808020208080202080802020808020208080202080941410101414101014141010141410101414101014141010141410101414101282828282828282820200000202000002828282828282828202000002020000505050500010000050505050001000005050505000100000505050500010000a0800000a0800000a0800000a0800000a0800000a0800000a0800000a0800000000000141414100000000014141410000000001414141000000000141414100000000280028200000000028002820000000002800282000000000280028210101000101010001010100010101000101010001010100010101000101010000008080000080800000808000008080000080800000808000008080000080941400001414000014140000141400001414000014140000141400001414000000000000000000000000000000000002828282028282820282828202828282404040404040404040404040404040404040404040404040404040404040404808000008080000080800000808000008080000080800000808000008080000014001000140010001400100014001000140010001400100014001000140012828282028282820282828202828282028282820282828202828282028282825000500050005000500050005000500050005000500050005000500050005002020a0802020a0802020a0802020a0802020a0802020a0802020a0802020a0941414140000000014141414000000001414141400000000141414140000000282828282828282828282828282828282020000020200000202000002020000505050505050505050505050505050500000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a000000000000000141014101410141014101410141014101410141014101410141014101410141282828282020000028282828202000002828282820200000282828282020000505050005050500050505000505050005050500050505000505050005050500
|0,1=>0xa0a00000a0a000000000000000000000a0a00000a0a000000000001414101000000000141410100000000014141010000000001414101080808080808080808080000080800000808080808080808080800000808000101050500000000010105050000000001010505000000000101050500000000808080800000808080808080000080808080808000008080808080800000808000000000000000040400000404000000000000000000000404000004040002020202020202020282820202828202020202020202020202828202028282021010000010100000101000001010000010100000101000001010000010100000000000000000000a0a0a000a0a0a0000000000000000000a0a0a000a0a0a014141414141414141414101014141010141414141414141414141010141410100200020002000200020002000200020002000200020002000200020002000250505050505050500040004000400040505050505050505000400040004000400200000002000000020000000200000002000000020000000200000002000141414141414000014141414141400001414141414140000141414141414000282828282828282828280000282800002828282828282828282800002828000505050505050505040404040404040405050505050505050404040404040404a0200000a0200000a0200000a0200000a0200000a0200000a0200000a02000040014000400140004001400040014000400140004001400040014000400140202020202828202020202020282820202020202028282020202020202828202000000005050000000000000505000000000000050500000000000005050000
|_,_=>0
def stPool : Nat → Nat
|0=>0x31910318830e4c40c621710318c3981031885971031822c00c620558418800c5440c830e5040c63130040c830e4840ce3084441832103c60c838c3460c800c1440c62c82840c800c0441832092c318520a1832091441832071830050840c2040
|1=>0x4418e20ca040c620c3a71060c838c4040c83161a61060ce00c0841883a532410318830e8c40c620238b10318e3221060c800c3c40c818e32110320c58680418320e31e10318e3087440c838c19c1031882d61033883026c40c638c218106383
|2=>0x3b310330818e9840c620e30b10330818e80418321f30f10320e306c841880ce33110320e33010318e31810320638cbc41880cc3ae10318830e5840c638c20a1060c838c2441880ce32d1031883ec1063083ab0c620e30510620c383a840c838c
|3=>0x10318e20c10318838c5840c620e30f1063080ce9440c63883291060cc20e00418c203
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x14507a82940aa005
|5,0=>0x3929b18ccc6062da95589ec49621b0f586ec31615b09583ec196
|6,0=>0xb13d6dea8f4e6a43505e74f337963c95e3cf186893431a0aeff67cb3c9dd6ee476ebb59d9eec876132edd68ead7533a7dd30e92645ba11cfcc777
|7,0=>0x1a17cd3e4df18f857bf3dddee0f697
|8,0=>0x1a86
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 52 then fld (dictB (i / 512) (i / 32 % 16)) 251 (i % 32) else 0
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
|0=>0xe3138c833920c88390ce863938c063a18bce3020b4e30320c63a38f4e3200c483938cce320c0883910b4e3018b4e300e9483208e883100cc83918e4c3920c48390cc433930e083120bce3038c883931f483a20f4e3238c4e30182883121a433258bce3138c0e3110b4e30
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xcc000000000c000000000000000000000000000
|6,0=>0x322c0ae2002c2002a20028298a4200222809e2709a260962001424890200000388c2000a22080018800
|7,0=>0x3c1ec7a1e4781dc761d4741
|8,0=>0x3d0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 10 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x1000000000400000000000000000000000000000000000
|6,0=>0x10010240000100000c10000310014300000310010400028040c0200000002003002000000022040000011006000001000
|7,0=>0x3f2373af0d30e53a996ba33165
|8,0=>0x1cf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 12 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_122,7,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 1 then [(dom_242,6,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 2 then [(dom_218,6,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 3 then [(dom_186,6,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 4 then [(dom_248,5,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 5 then [(dom_234,5,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 6 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 7 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 8 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 9 then [(dom_184,4,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 10 then [(dom_120,4,runOps true dom_120 (0,roots_120) ops)] else [])++(if pm.testBit 11 then [(dom_202,4,runOps true dom_202 (0,roots_202) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_250 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_122 _ g hchk
    · exact cpcs (by decide +kernel) low_242 _ g hchk
    · exact cpcs (by decide +kernel) low_218 _ g hchk
    · exact cpcs (by decide +kernel) low_186 _ g hchk
    · exact cpcs (by decide +kernel) low_248 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_184 _ g hchk
    · exact cpcs (by decide +kernel) low_120 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_122 7 s (0, roots_122) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_250 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_122 h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_250 == dom_250) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_250 goalM v ys) : RunD true dom_250 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_250 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 36 → Z 6 i = true := (range_split (range_split z6_0 z6_12) z6_24)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_250 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_250 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_250 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_250 roots_250 goal_250 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_250

theorem low_250 : Lower true dom_250 roots_250 goal_250 9 := S_250.noCircuit

theorem low_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_slice (d:=dom_209) (dSub:=dom_81) (T:=goal_209) (TSub:=goal_81) (roots:=roots_209) (rootsSub:=roots_81)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30003000000000003000300000000000000000000000000000000, 16, 144)] (by decide +kernel) (by decide +kernel) low_81

namespace S_211
def pairsG : List (Nat × Nat) := [(1,17), (1,65), (2,18), (2,130), (3,19), (3,67), (3,131), (16,17), (16,18), (16,80), (16,144), (64,65), (64,80), (66,67), (66,82), (66,194), (128,130), (128,144), (129,131), (129,145), (129,193), (192,193), (192,194), (192,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
|3=>0x1
|4=>0x4
|5=>0xa
|6=>0x4
|7=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x1173b
|4,0=>0x25c7916cd409f5e00942
|5,0=>0x6f2454da443fcd63cc4738591325512507b215ba18c590397e
|6,0=>0xc246730d9b15e940570a
|7,0=>0xc2467
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f00000000000c000c00000000000f000f00000000000c000c500000000000000050000000000000005000000000000000500000000000000000000f000c000000000000000000000000000f000cf000a00000000000f000a00000000000f000a00000000000f000a0000000000000000f000a000000000000000000000000000f000a5000500000000000500000000000000050005000000000005000000000000000000000000000000000000f000000000000000f0000f000f000000000000000000000000000f000f00000000000f0000f000f00000000000f000f00000000000f000f0000000000000000f000f00000000000f000000000000000f000f00000000000f000000000000000000000000000000000000500000000000000050000f000f00000000000f000f00000000000f000a00000000000f000a0000f000000000000000f000000000000000f0000000000000000f000f00000000000f000f00000000000a000a00000000000a000af000000000000000f000000000000000a000000000000000a00000000000000000000f000f000000000000000000000000000f000a50005000000000001000000000000000500050000000000010000f000c00000000000f000c00000000000f000c00000000000f000ce000000000000000e000000000000000e000000000000000e0000f000f00000000000f000f00000000000000000000000000000000c000c00000000000c000c00000000000c000c00000000000c000cf000000000000000f000000000000000f000000000000000f0000f000a00000000000e000a00000000000f000a00000000000e000aa000a00000000000a000a00000000000a000a00000000000a000af000f000000000000000000000000000f000f0000000000000000f000f00000000000f000f00000000000f000000000000000f0000f000c00000000000f000c00000000000f000c00000000000c000c
|_,_=>0
def stPool : Nat → Nat
|0=>0x1c4530ce22986230ca7a0ce511b47118a3b9c462df27194c2c1cc51dec731455198a714cc33c8b1308e32c0c238caf198472b8c238cac31c6559ca6128471a507308a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>0x26b47682cf15b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 27 then fld (dictB (i / 512) (i / 32 % 16)) 212 (i % 32) else 0
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
|0=>0x29f11928db8f28d15e28d15129f28938969538d69438d
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa2008200624200220002
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
|5,0=>0x440140418030039
|6,0=>0x3eff5a
|7,0=>0x3b
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 1 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 2 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 3 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 4 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 5 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_211 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_209 _ g hchk
    · exact cpcs (by decide +kernel) low_147 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
    · exact cpcs (by decide +kernel) low_146 _ g hchk
    · exact cpcs (by decide +kernel) low_81 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_210 5 s (0, roots_210) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_210 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffffffffffffffff0000000000000000, 64)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_211 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_211 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_211 roots_211 goal_211 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_211

theorem low_211 : Lower true dom_211 roots_211 goal_211 8 := S_211.noCircuit

theorem low_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_slice (d:=dom_243) (dSub:=dom_211) (T:=goal_243) (TSub:=goal_211) (roots:=roots_243) (rootsSub:=roots_211)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_211

theorem low_201 : Lower true dom_201 roots_201 goal_201 5 :=
  lower_slice (d:=dom_201) (dSub:=dom_73) (T:=goal_201) (TSub:=goal_73) (roots:=roots_201) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000030300000000000000000000000000000000, 8, 136)] (by decide +kernel) (by decide +kernel) low_73

theorem low_201_l128 : Lower true dom_201 roots_201 goal_201_l128 5 :=
  lower_slice (d:=dom_201) (dSub:=dom_73) (T:=goal_201_l128) (TSub:=goal_73) (roots:=roots_201) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000030300000000000000000000000000000000, 0, 128)] (by decide +kernel) (by decide +kernel) low_73

theorem lowZ_201_2_128 : Lower true dzo_201_2 roots_201 gzo_201_2_128 5 :=
  lower_iso (d1:=dom_201) (roots1:=roots_201) (T1:=goal_201_l128) [(dom_201, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_201_l128

namespace S_203
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,130), (3,11), (3,67), (3,131), (8,9), (8,72), (8,136), (10,11), (10,74), (10,138), (64,65), (64,72), (66,67), (66,74), (66,194), (128,130), (128,136), (129,131), (129,137), (129,193), (192,193), (192,194), (192,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_203.map (· &&& dom_203)
def goalM : Nat := goal_203 &&& dom_203
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x1765103191
|5,0=>0xbc17e1f0e807e6e
|6,0=>0x6b015
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0000000000000a0a0000000000000f0f0000000000000a0a500000000000000050000000000000005000000000000000500f0f0000000000000f000000000000000f0f0000000000000f00f0f00000000000000000000000000000f0f0000000000000000505000000000000050000000000000005050000000000000500f0f0000000000000f0f00000000000000000000000000000000c0c0000000000000c0c0000000000000c0c0000000000000c0cf000000000000000f000000000000000f000000000000000f00a0a0000000000000a0a0000000000000a0a0000000000000a0af0a00000000000000000000000000000f0a0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x462314236194632184132674326543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 204 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 9 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x18521c99
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x21441
|6,0=>0x30
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 6 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x10e8
|6,0=>0x1f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_201,5,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 1 then [(dzo_201_2,5,runOps true dzo_201_2 (0,roots_201) ops)] else [])++(if pm.testBit 2 then [(dom_202,4,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 3 then [(dom_139,4,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 4 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_203 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_201 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_201_2_128 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
    · exact cpcs (by decide +kernel) low_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_201 5 s (0, roots_201) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_203 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_201 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
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

theorem low_203 : Lower true dom_203 roots_203 goal_203 7 := S_203.noCircuit

theorem low_233 : Lower true dom_233 roots_233 goal_233 6 :=
  lower_slice (d:=dom_233) (dSub:=dom_201) (T:=goal_233) (TSub:=goal_201) (roots:=roots_233) (rootsSub:=roots_201)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000000000003030000000000000303000000000000030300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_201

theorem low_233_l160 : Lower true dom_233 roots_233 goal_233_l160 6 :=
  lower_slice (d:=dom_233) (dSub:=dom_201) (T:=goal_233_l160) (TSub:=goal_201_l128) (roots:=roots_233) (rootsSub:=roots_201)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000000000003030000000000000303000000000000030300000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_201_l128

theorem lowZ_233_2_160 : Lower true dzo_233_2 roots_233 gzo_233_2_160 6 :=
  lower_iso (d1:=dom_233) (roots1:=roots_233) (T1:=goal_233_l160) [(dom_233, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_233_l160

theorem low_227 : Lower true dom_227 roots_227 goal_227 5 :=
  lower_slice (d:=dom_227) (dSub:=dom_163) (T:=goal_227) (TSub:=goal_163) (roots:=roots_227) (rootsSub:=roots_163)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f00000000000000000000000f0000000f0000000000000000, 1, 65)] (by decide +kernel) (by decide +kernel) low_163

namespace S_235
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,34), (2,130), (3,11), (3,35), (3,67), (3,131), (8,9), (8,40), (8,72), (8,136), (10,11), (10,42), (10,74), (10,138), (32,33), (32,34), (32,40), (64,65), (64,72), (66,67), (66,74), (66,98), (66,194), (96,97), (96,98), (96,104), (128,130), (128,136), (129,131), (129,137), (129,161), (129,193), (160,161), (160,162), (160,168), (192,193), (192,194), (192,200), (224,225), (224,226), (224,232)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_235.map (· &&& dom_235)
def goalM : Nat := goal_235 &&& dom_235
def NN : Nat → Nat
|4=>0x5
|5=>0xf
|6=>0x25
|7=>0xa
|8=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xc5688badaa8052041d993dadb
|5,0=>0xf0315ee774e2f99ba470abd2fa0e5d9edc28ffa3806477c37b77b796270e5f137456cd31ff8
|6,0=>0xf7097f58aeef612ef42fecff9e1408d5f27cf3d5cd38bbc871bad2ab8e71ab3cea6ffba0e5d9e4389ccb898b2c96df795d3a8f2f28bdfe8b3958a8c57c4a2620db61d9c574f95365b4c0473cb513b10b2ec6a2ea6429bf9088e302ce7
|7,0=>0xfe1f7fb139f46f1ee89bcbbe4b760d9ccb874cb75b92116e38
|8,0=>0xf0b1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f00000f0f00000f0a00000f0a00000f0f00000f0f00000f0a00000f0a40c0000040c0000040c0000040c0000040c0000040c0000040c0000040ce0c00000e0c00000e0c00000e0c00000e0c00000e0c00000e0c00000e0c000000000000000000a0000000a00000000000000000000000a0000000af0f00000f0f00000f0f00000f0f00000a0000000a0000000a0000000a0050000000500000005000000050000000500000005000000050000000500d0c00000d0c00000d0c00000d0c00000d0c00000d0c00000d0c00000d0cf0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0a00000a0af0f00000f0f00000f0000000f0000000f0f00000f0f00000f0000000f00f0f00000f0f00000a0000000a0000000f0f00000f0f00000a0000000a00a0a00000a0a00000f0a00000f0a00000a0a00000a0a00000f0a00000f0a00c0000000c0000000c0000000c0000000c0000000c0000000c0000000cf0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00f0000000f0000000a0000000a0000000f0000000f0000000a0000000af0a00000f0a000000000000000000000f0a00000f0a0000000000000000f0f00000f0f000000000000000000000f0f00000f0f0000000000000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a000000000000000000a0a00000a0a000000000000000000000a0a00000a0af0000000f0000000f0a00000f0a00000f0000000f0000000f0a00000f0a0000000000000000f0000000f00000000000000000000000f0000000f00f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0a00000f0f0000000000000f0f00000f0a00000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0f00000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000050a0000050a0000050a0000050a0000050a0000050a0000050a0000050a000000000000000050a0000050a00000000000000000000050a0000050af0f00000f0f00000f0f00000f0f00000000000000000000000000000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f00000a0000000f0f00000a0000000f0f00000a0000000f0f00000a00f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a0000000000000000f0a00000f0a000000000000000000000f0a00000f0a
|0,1=>0x80c0000080c0000080c0000080c0000080c0000080c0000080c0000080cf0f00000f0f0000000a0000000a00000f0f00000f0f0000000a0000000ac0c00000c0c00000f0c00000f0c00000c0c00000c0c00000f0c00000f0c50f0000050f00000000000000000000050f0000050f0000000000000000a0a00000a0a0000000a0000000a00000a0a00000a0a0000000a0000000a00a0000000a0000000a0000000a0000000a0000000a0000000a0000000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xcb29b1101cb2991070cb0503840cb2812444070c61070c16171070d60444030811070cb2801070ce2d51072802d41072802d31101c304610740a4d21032ca2441c33c10041c304e3041c328d3032ca2481070c11441c30061070c61440c2040
|1=>0x4070e06844070ca2c11070cb2907c41d028e2d31070ca0503041c32814171101ca04b5041c340a2d21070ca60b5c44072812d31101cb29e1070cb2961070cb2900044032ca0844072ca7441c340b29c10740a60b4c41c32ca4441c32ca040407
|2=>0x4070cb2811101c32ca3c41cb0d02981101c32ca6844072ca9441c32ca4241070d028b3441c340b2951070ca38b3041ca40b8c41c32e04181070cb2a21101c33c11070cb2814444072a02d41070d02ca8444072a02d31070cb0506041c32ca004
|3=>0x44072c328440728b5041c32902cc1070ca40b5c440728b4c44070cb2a01072c340a384
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x14507a82940aa005
|5,0=>0x1a58c8a5e62ca95149cc4862130f186cc30615a89583ec196
|6,0=>0x15f6ac3d45e94f4379eb4d9e60d2a691bc71e2af0e783bc059f6cf4776bb99dbeed8768bb29d86ebc75b32c1952ea364eb259d1ee8964139f18ecc6f7
|7,0=>0x346d9c7cabe3db10f817bd3dcded8f657
|8,0=>0x1a96
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 38 then fld (dictB (i / 512) (i / 32 % 16)) 236 (i % 32) else 0
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
|0=>0x40b8b0d2ca90292ca50062ca4b2b2ca8b812ca8b0d40a902e2ca502d2ca4b0e2ca502d40a4b0d2ca433f2ca103d2ca073d2ca033d2ca0b0d40a50042ca50062ca443d2ca03692cad02a2ca47454010b2904fcb292ca102d40a4b292ca503d2ca0b291cf4b2804fcb292ca07454010b29
|1=>0xb0e40b902d2c34b2a40a8b292ca10292cac36b2cac33140b90292ca903f2ca0b292ca10042ca4b0e2ca8a33
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x48c798c312618c000000000001980000600000000
|6,0=>0x4d20000000000096524a39452865049f93d2764e49b9352000cc9892f25a4001592924e494800232424000f91d2364648b9152
|7,0=>0x2c0d71ac3546a0d31a4344680cf1
|8,0=>0x590
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 11 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x20080600807000000000000800008080000000
|6,0=>0xd000000000003410106018004014040840011860000010142103000080200034610014003400802110404103430
|7,0=>0x37cdb97e1f1febf1fe6fafe6f
|8,0=>0x1f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 10 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 1 then [(dom_107,7,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 2 then [(dom_233,6,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 3 then [(dzo_233_2,6,runOps true dzo_233_2 (0,roots_233) ops)] else [])++(if pm.testBit 4 then [(dom_171,6,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 5 then [(dom_234,5,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 6 then [(dom_227,5,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 7 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 8 then [(dom_202,4,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 9 then [(dom_163,4,runOps true dom_163 (0,roots_163) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_235 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) low_233 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_233_2_160 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_227 _ g hchk
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_203 7 s (0, roots_203) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_235 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_203 h

def symsG : List (List (Nat × Nat)) := []
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_235 == dom_235) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_235 goalM v ys) : RunD true dom_235 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_235 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_36 : ∀ i, 36 ≤ i → i < 37 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 36 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 37 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 10 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_235 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_235 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_235 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_235 roots_235 goal_235 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_235

theorem low_235 : Lower true dom_235 roots_235 goal_235 9 := S_235.noCircuit

theorem low_219 : Lower true dom_219 roots_219 goal_219 9 :=
  lower_slice (d:=dom_219) (dSub:=dom_211) (T:=goal_219) (TSub:=goal_211) (roots:=roots_219) (rootsSub:=roots_211)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) low_211

theorem low_249 : Lower true dom_249 roots_249 goal_249 8 :=
  lower_slice (d:=dom_249) (dSub:=dom_121) (T:=goal_249) (TSub:=goal_121) (roots:=roots_249) (rootsSub:=roots_121)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303030303030303030303030303030300000000000000000000000000000000, 8, 136)] (by decide +kernel) (by decide +kernel) low_121

theorem low_249_l176 : Lower true dom_249 roots_249 goal_249_l176 7 :=
  lower_slice (d:=dom_249) (dSub:=dom_233) (T:=goal_249_l176) (TSub:=goal_233_l160) (roots:=roots_249) (rootsSub:=roots_233)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000030300000303000003030000030300000303000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_233_l160

theorem lowZ_249_2_176 : Lower true dzo_249_2 roots_249 gzo_249_2_176 7 :=
  lower_iso (d1:=dom_249) (roots1:=roots_249) (T1:=goal_249_l176) [(dom_249, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_249_l176

theorem low_241 : Lower true dom_241 roots_241 goal_241 6 :=
  lower_slice (d:=dom_241) (dSub:=dom_209) (T:=goal_241) (TSub:=goal_209) (roots:=roots_241) (rootsSub:=roots_209)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3000300000000000300030000000000030003000000000003000300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_209

theorem low_217 : Lower true dom_217 roots_217 goal_217 6 :=
  lower_slice (d:=dom_217) (dSub:=dom_209) (T:=goal_217) (TSub:=goal_209) (roots:=roots_217) (rootsSub:=roots_209)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3000300000000000300030000000000030003000000000003000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_209

namespace S_251
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (1,65), (2,18), (2,34), (2,130), (3,11), (3,19), (3,35), (3,67), (3,131), (8,9), (8,40), (8,72), (8,136), (10,11), (10,26), (10,42), (10,74), (10,138), (16,17), (16,18), (16,80), (16,144), (24,25), (24,26), (24,56), (24,88), (24,152), (32,33), (32,34), (32,40), (48,49), (48,50), (48,56), (48,112), (48,176), (64,65), (64,72), (64,80), (66,67), (66,74), (66,82), (66,98), (66,194), (96,97), (96,98), (96,104), (96,112), (128,130), (128,136), (128,144), (129,131), (129,137), (129,145), (129,161), (129,193), (160,161), (160,162), (160,168), (160,176), (192,193), (192,194), (192,200), (192,208), (224,225), (224,226), (224,232), (224,240)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
|5=>0xa
|6=>0x5f
|7=>0x195
|8=>0x174
|9=>0x63
|10=>0xd
|11=>0x1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0xeb2b5d3924895d67bffd5bb3e4684e452992bbbe1762708daf
|6,0=>0xfce53f9621f1a5ce4f84e396be0b70dc5fbdc19ddb74ed8b55d20d1cd9c9caabfc8c57c8b4fc788dc3ddac0b7ec079ec0329bdc99bbc15b77deb7256b287eadbd4ad126a6ef0a5621a40e5a3d0e9f6d39d6fb9b0709608095da39348a91cca8f44b89c92893ae8521482da67b45878bca7617875f8371a3a6fb696ddb2678ec640f660e00609755e3275dc645b05255fe755507546d553ca64e19348cd248ac345b324365c40f91409b4401513f0033d69c3cd8d3a9c0330a9310c72b9af2b76f296f5273c5251bb23a3423702235832329f2066f1f1ef1d2b51c227195d2159a114b0d113bf0d327091a6031b5
|7,0=>0x5508554342529f15065a5000f4fb4f4f17d4ef754e3ab4d9b24d7e14d6c14d1a14c7d94b4614b3874b13e4a83149e8148dfe488c1487574848f4715046b3c4366f429d5423124206441c92407134056b3f0b53ea6b3e0273d69c3d53c3d3273cdfb3cbf53b8953b5cb398933909238f0a38945384493752536190353c434f0434d203436333723329f531d16314653123a30fa52fe842f8542dee82d4b22b81c2ac972a69628e4a28e2e285d02804927a682615825d542581a2567c24dda24d6b24a41231a22283b226fa2202421dca213831efeb1ec711e7881e4471e01a1daa41d2b51c8d11c2df1bcf21ae4f1aca51a4e819dfd1994c194cc18cdc1746b168c21638a157151468f1338212f5d127a111bc2119de0f3530ed290df4a0d27c0d0c10ccac0bbf40b50d09e85084c60836a075ae0664704b61033cf03087016b9
|7,1=>0xa5621a5405a4e20a473ca45dda3851a3540a2a46a2a34a22dca1da6a02ef9fd3d9f2279e4609e06b9dc779d96e9c01f9b1549afe09ac039a4ad99c4199a5e9957b995159913b9909298f9498e48969ab94bf19420493e7b9333291dcc91aaf8fd5c8f4d58f44b8e4138d24e8cb188bd2d8ba3a8abc98a53c89fed89c008919787fec87e828506c84b548481a8471e83ce7836958232a805c17fe887fe7f7e4dc7e4947e3497df857defb7cca37c7bd7ab07792ad79230781ad7669675a4d752d174b1c74129736ff728b072603715bb7133370ec9707c4706226f71f6f13f6ea9b6e9e06d9d36d5606d3f96cf4a6bcb86a5ca6a14869be6694db684c76710c66eae6625a6603365482651bd64ac56478a62f9d62e57625ac60abb5f77f5e86b5e7855da745c6005b6895b3e55abec593f05818757f9357ae256c0d55e1355c14
|7,2=>0xf4ad9f39aef3977f3219f3053f29f8f1562f0f4ff0d3ff01a8ef8c4ee7c1edd4ced30cecfbdecbb5ebfc5ebafceb6f7eabd2ea9a9e9dc7e924fe8886e77e7e71eee5ef7e58fae549ce50fbe4f4ce4213e3f58e3a65e3542e3163e2a0ce1c67e067fdfe55df681ded55de4b3de277ddb8fdcd6fd9f5fd8bf3d7808d6fb5d6caed4583d28a9d20d1d1df2d1a88d157ed073dcf5d4cf130cf07bce671ce013cdef2cd6ecccf85ccf00cacaecac22ca60cca492ca15bc98aac9035c8c57c7a36c77fbc714ac6de1c6a2fc670ac668fc65a9c5da4c570bc4f0cc3158c288ec1c91c0b7ec0486c03a1c034dbee9dbea3abe950be005bddd6bd4a4bd0b2bc55fbbb33bb835ba38fb9bc2b89e8b6863b4d6db47a7b3a93b3a77b221bb1bbcb0e32b0a28b0534af751ae9d3ae407ad762acb5aac10bab2bfab23faa7bfa9dd4a789fa691d
|7,3=>0xff90cff470feed7fe8dbfe23afc4d9fc384fb977faacafa554f99c5f8c86f7db2f7bfbf790df6aedf69a8f6935f527af4fb4f4ea6
|8,0=>0x60f0a60d26603a06007d5e0ca5e08d5ce085ca775c3705bc215b0305a78a5a678592ad590a5525bf51ec851af15130350f3250ef7506b85065a501724fb7f4f17d4ef754d8ef4d01d4c5cd4bf784b1254a7e24848f474de44cbf433a7431d84303a41bc8417e2417df415313fd783fd5a3f9993f2793ef943e0273db233b13a3a7013a3b43980f396523909e38f0a38e7c38a9f3736c360ad35c48353dc348d63472c2fadc2ef372e55b2d5b52d5742d5322b76c2b4312a7a62a4092a17428da12830a25ca12578824d3923a5f238652340221997202d91fe841ec711e5081de621dddf1d5c21d2b51ca271ae9f1acae18fb714ec1143d81286f12143120d3101190feaf0f8d60e4ea0e2f50d0c10b24b0ad91094e408ecb0858507041066470634e0608905d650325202d2902ce102b51029400204700f1c00cdb00c1d000e2
|8,1=>0xbc1e0bbb33bb989baaedb9bc2b923fb8e7eb806cb7bdeb7283b7159b6eeab6957b6444b5b36b4a04b3d99b3a77b3139b1b25ae90bae8bfadf3cabd1bab2bfaa41ea96e5a96a1a945ca8a9da8a59a7e72a6e33a5a80a4fbda4eeca4957a3d11a3b05a3a52a3817a2999a1dbc9e4609de6b9c80e9c62d9c5c89c5449b8da9b41a9afe099be1999d5979e49770697112954ea94ecf94ddd94a4d94333929c99268c92425920119113090e6e905af90274902288eb048ea6a8e8cb8ceb38a6f1895bb8841787f818614485b5c856748495d8471e846168316982f8282df08272e80cde80a64806e7805c17fe7f7fa117e8487e32f7de517db2f7d4597b6d37b5447a8bb79e5a74fdc7291971a237169470f157078b6fef96f8656f13f6e1066ba7f6a3fa69d2869d25698e567c9f66f7a66b9166570664a062f9d6153f6148460fe0
|8,2=>0xfff85ff3aaff35efed9bfe2b7fda9bfd487fd431fcf11fc4d9fc256faa30f95eef6decf6aedf610ef55f9f527af4b46f3941f320bf2126f1d65f195df0d3feeec9ed13ceb627eac0bea11ee9dc7e9d79e924fe7f74e7b18e64cee64bde6294e618ce5fcce59eae485fe4502e3bb9e2452e23d5e07c1df746defe6deac9de94bde8d9de538de277ddaaddd980dd7ffdd3b8dc39edc05cdbcd3da6a1da2f4d9862d97f1d95dbd905bd8b19d7030d451fd42ead3850d3288d1d29d192bd0f06d0b5fd0571d0564cfffacf83bccf00ccc00cc3a8cb933cb61fcad35ca395ca0aac9683c9384c9035c820fc7f14c7bf9c77fbc71e2c6a2fc6434c5c63c570bc4f89c4c73c476dc375ac345fc2faec2ad0c14efc00febf5b0bdf61bde95bda05bd0b2bccd9
|9,0=>0xff3aafbd13f9845f527af2c3feebd1ed13cecd5be9dc7e83e1e4837e2bd5e2ba3dbcd3daa74d9d4ec7b06c29e5bc7ecb86feb7173b5d61b4b58af31aaec83ae00aadad9ac669ab071a3d05a215aa1a5c9e8a69e6f69a65197fe1902e18dbb18d1f28abe5870178677882bb581c5880ab57cf107a78178a2d773e173259721e670fa9703756b7956b74f6a690680b6677c7651b962f9d619155ebfa5bac45706e547964eb4f4a666483924124940e3d3f4ac371a3370ae36d0d36afa3537c3532d306cd2ef3728db5285e9272a926bf92493b24774229541f1311a80b16c3b1660013a3b107770f12c0e2250dad20d90b0d2b6081b406647
|10,0=>0xeefa6e2ce9d7fedcc047c72f8b4bcfa0f4199e5793a6f861b16166554aca0f948
|11,0=>0xcdebd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c303030c0303030c0303030c0303030c0303030c0303030c0303030c0303030c00000000f000f0e000000000f000f0e000000000f000f0e000000000f000f0ef0f0c0c0a0a08080f0f0c0c0a0a08080f0f0c0c0a0a08080f0f0c0c0a0a0808f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e2020606020206060202060602020606020206060202060602020606020206063030303030302020303030303030202030303030303020203030303030302020000f0f00000e0e00000f0f00000e0e00000f0f00000e0e00000f0f00000e0ef0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f0000f040e000f040e000f040e000f040e000f040e000f040e000f040e000f040e00b000e000b000e000b000e000b000e000b000e000b000e000b000e000b000e0000000000000000f0f0f0a0f0f0f0a00000000000000000f0f0f0a0f0f0f0ac0c0c0c0c0c0c0c03030306030303060c0c0c0c0c0c0c0c0303030603030306f000f0c0f000f0c0f000f0c0f000f0c0f000f0c0f000f0c0f000f0c0f000f0c0000000000000000b0b0f0e0b0b0f0e00000000000000000b0b0f0e0b0b0f0ef0f0f0f0a0e0a000f0f0f0f0a0e0a000f0f0f0f0a0e0a000f0f0f0f0a0e0a0000000000000000000000000000000000b0b0f0e0b0b0f0e0b0b0f0e0b0b0f0ef0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0ae0e0e000e0e0e000e0e0e000e0e0e000e0e0e000e0e0e000e0e0e000e0e0e00100010c0100010c0100010c0100010c0100010c0100010c0100010c0100010cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a3030f0c03030f0c03030f0c03030f0c03030f0c03030f0c03030f0c03030f0c00000000b0b0f0e000000000b0b0f0e000000000b0b0f0e000000000b0b0f0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0ac0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0a0e0a000a0e0a000f0f0f0f0f0f0f0f0a0e0a000a0e0a00
|0,1=>0x505050c0505050c0505050c0505050ca0e0a000a0e0a000a0e0a000a0e0a000a0e0a000a0e0a000a0e0a000a0e0a0000000000a0a0a0a000000000a0a0a0a000000000f0f0f0e000000000f0f0f0e000000000000000030303020303030200000000000000000303030203030302c0c0c0c0c0c0c0c00000004000000040c0c0c0c0c0c0c0c0000000400000004f0f0f0f0f0f0f0f00040004000400040f0f0f0f0f0f0f0f000400040004000400000000f0f0f0f000000000f0e0f0e000000000f0f0f0f000000000f0e0f0e00000000f0a0f0e000000000f0a0f0e000000000f0a0f0e000000000f0a0f0ef0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e303060603030606030306060303060603030606030306060303060603030606000000000000000050505000505050000000000000000000505050005050500000000000000000000f000a000f000a0000000000000000000f000a000f000af0f02020f0f06060f0f02020f0f06060f0f02020f0f06060f0f02020f0f0606505050505050404050505050505040405050505050504040505050505050404c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c08080c0c0808f0f0f0f0c0c08080f0f0f0f0c0c08080f0f0f0f0c0c08080f0f0f0f0c0c08080000000000000000a0a0a0a0a0a0a0a00000000000000000f0f0f0e0f0f0f0e30307000303070003030700030307000303070003030700030307000303070030303030303060603030303030306060303030303030606030303030303060600000000000000000000000000000000d0d0d0c0d0d0d0c0d0d0d0c0d0d0d0c00000000c0c0c0c000000000f0f0f0e000000000c0c0c0c000000000f0f0f0e303020203030202030302020303020203030202030302020303020203030202505050405050504050505040505050405050504050505040505050405050504000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000cf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c3030300030303000303030003030300030303000303030003030300030303000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0ae0e0e0e020206060e0e0e0e020206060e0e0e0e020206060e0e0e0e02020606f0c0a080f0c0a080f0c0a080f0c0a080f0c0a080f0c0a080f0c0a080f0c0a08c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c00f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c
|0,2=>0xc0c0c0c0c0c0c0c0f0f0f0e0f0f0f0ef0f0f0a0f0f0f0a00040000000400000f0f0f0a0f0f0f0a0004000000040000004000400040004000400040004000400040004000400040004000400040004f0f0f0f0f0f0f0f0a0e0a0e0a0e0a0e0f0f0f0f0f0f0f0f0a0e0a0e0a0e0a0ef0f0f0f0f0f0f0f0f040f040f040f040f0f0f0f0f0f0f0f0f040f040f040f04f0f0a0a0c0c08080f0f0a0a0c0c08080f0f0a0a0c0c08080f0f0a0a0c0c08080000000000000000f0b0f0a0f0b0f0a00000000000000000f0b0f0a0f0b0f0a0000000000000000f0f0f0e0f0f0f0e00000000000000000f0f0f0e0f0f0f0e303030603030306030303060303030603030306030303060303030603030306f0f0f0f020206060f0f0f0f020206060f0f0f0f020206060f0f0f0f0202060650505000505050005050500050505000505050005050500050505000505050000f000a000f000a000f000a000f000a000f000a000f000a000f000a000f000a00000000000000000000000000000000f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e0000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e0000000000000000c0c0c080c0c0c0800000000000000000c0c0c080c0c0c08c0c0c0c0c0c0c0c0f0f0f0e0f0f0f0e0c0c0c0c0c0c0c0c0f0f0f0e0f0f0f0e101010c0101010c0101010c0101010c0101010c0101010c0101010c0101010c003050000030500000305000003050000030500000305000003050000030500f0f000c0f0f000c0f0f000c0f0f000c0f0f000c0f0f000c0f0f000c0f0f000cb0b0b0a0b0b0b0a0b0b0b0a0b0b0b0a0b0b0b0a0b0b0b0a0b0b0b0a0b0b0b0a00000000f0e0f0e000000000f0e0f0e000000000f0e0f0e000000000f0e0f0e0000000000000000f0f00000f0f0f0e00000000000000000f0f00000f0f0f0ef0c0f080f0c0f080f0c0f080f0c0f080f0c0f080f0c0f080f0c0f080f0c0f083030302030303020303030203030302030303020303030203030302030303020000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e303070603030706030307060303070603030706030307060303070603030706b0b0f0e0b0b0f0e0b0b0f0e0b0b0f0e0b0b0f0e0b0b0f0e0b0b0f0e0b0b0f0ec0c080a0c0c080a0c0c080a0c0c080a0c0c080a0c0c080a0c0c080a0c0c080a000000000000000000000000000000003030f0c03030f0c03030f0c03030f0c00000000f0f0e0e000000000f0f0e0e000000000f0f0e0e000000000f0f0e0e20202020202060602020202020206060202020202020606020202020202060600f000e000f000e000f000e000f000e000f000e000f000e000f000e000f000e
|0,3=>0x50400000504000005040000050400000504000005040000050400000504000000400000004000000040000000400000004000000040000000400000004f0f0f0f0f0f0f0f00000004000000040f0f0f0f0f0f0f0f00000004000000040000c0e00000c0e00000c0e00000c0e00000c0e00000c0e00000c0e00000c0e000000000000000000000000000000005050504050505040505050405050504000000000000404000000000000040400000000000004040000000000000404a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e0a0e000040400000404000004040000040400000404000004040000040400000404d0d0d0c0d0d0d0c0d0d0d0c0d0d0d0c0d0d0d0c0d0d0d0c0d0d0d0c0d0d0d0cf0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0ea0a0a0e0a0a0a0e0a0a0a0e0a0a0a0e0a0a0a0e0a0a0a0e0a0a0a0e0a0a0a0e101010001010100010101000101010001010100010101000101010001010100f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0ac0c0c0c0c0c08080c0c0c0c0c0c08080c0c0c0c0c0c08080c0c0c0c0c0c0808c0c0c080c0c0c080c0c0c080c0c0c080c0c0c080c0c0c080c0c0c080c0c0c08e0e02020e0e02020e0e02020e0e02020e0e02020e0e02020e0e02020e0e0202f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e00000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0af0f04040f0f04040f0f04040f0f04040f0f04040f0f04040f0f04040f0f040400000000000000000000000000000000f0f00000f0f0f0e0f0f00000f0f0f0e0040004000400040f0f0f0e0f0f0f0e00040004000400040f0f0f0e0f0f0f0e30302060303020603030206030302060303020603030206030302060303020630303030303030303020302030203020303030303030303030203020302030200f0c0e000f0c0e000f0c0e000f0c0e000f0c0e000f0c0e000f0c0e000f0c0ef0f0f0e0f0f0f0e00000004000000040f0f0f0e0f0f0f0e0000000400000004101000a0101000a0101000a0101000a0101000a0101000a0101000a0101000a000000e0000000e0000000e0000000e0000000e0000000e0000000e0000000e1010d0c01010d0c01010d0c01010d0c01010d0c01010d0c01010d0c01010d0c0000004000000040f0f0f0e0f0f0f0e00000004000000040f0f0f0e0f0f0f0e10105040101050401010504010105040101050401010504010105040101050400000000f0f0f0e000000000f0f0f0e000000000f0f0f0e000000000f0f0f0ee0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a
|0,4=>0xa0b0a000a0b0a000a0b0a000a0b0a000a0b0a000a0b0a000a0b0a000a0b0a0030f020e030f020e030f020e030f020e030f020e030f020e030f020e030f020ec000c040c000c040c000c040c000c040c000c040c000c040c000c040c000c04c0f0c0e0c0f0c0e0c0f0c0e0c0f0c0e0c0f0c0e0c0f0c0e0c0f0c0e0c0f0c0ef0f05040f0f05040f0f05040f0f05040f0f05040f0f05040f0f05040f0f0504f0f0f040f0f0f040f0f0f040f0f0f040f0f0f040f0f0f040f0f0f040f0f0f04f0f00040f0f00040f0f00040f0f00040f0f00040f0f00040f0f00040f0f0004f0f0f0f0f0f0e0e0f0f0f0f0f0f0e0e0f0f0f0f0f0f0e0e0f0f0f0f0f0f0e0ef030f020f030f020f030f020f030f020f030f020f030f020f030f020f030f0200004040f0f0e0e000004040f0f0e0e000004040f0f0e0e000004040f0f0e0ef0f0f0f030302020f0f0f0f030302020f0f0f0f030302020f0f0f0f03030202f000f040f000f040f000f040f000f040f000f040f000f040f000f040f000f04505050c0505050c0505050c0505050c0505050c0505050c0505050c0505050ca0a0a0a0a0a0e0e0a0a0a0a0a0a0e0e0a0a0a0a0a0a0e0e0a0a0a0a0a0a0e0ef0f00000f0f0e0e0f0f00000f0f0e0e0f0f00000f0f0e0e0f0f00000f0f0e0e003000200030002000300020003000200030002000300020003000200030002a0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e0a0a0e0e50501000505010005050100050501000505010005050100050501000505010000000000c0c0808000000000c0c0808000000000c0c0808000000000c0c0808c0c0c0c000004040c0c0c0c000004040c0c0c0c000004040c0c0c0c00000404e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e302030a0302030a0302030a0302030a0302030a0302030a0302030a0302030af000f0e0f000f0e0f000f0e0f000f0e0f000f0e0f000f0e0f000f0e0f000f0ef0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c005000400050004000500040005000400050004000500040005000400050004f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf050f040f050f040f050f040f050f040f050f040f050f040f050f040f050f04f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0af0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0af0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0ef0f0f0f00000e0e0f0f0f0f00000e0e0f0f0f0f00000e0e0f0f0f0f00000e0ef0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a0f0f0b0a
|0,5=>0xf0f0f0f050504040f0f0f0f050504040f0f0f0f050504040f0f0f0f05050404a0f0a0e0a0f0a0e0a0f0a0e0a0f0a0e0a0f0a0e0a0f0a0e0a0f0a0e0a0f0a0ef0f0f0f040404040f0f0f0f040404040f0f0f0f040404040f0f0f0f0404040400e000e000e000e000e000e000e000e000e000e000e000e000e000e000e000e303000203030002030300020303000203030002030300020303000203030002a0a0a0a0e0e0e0e0a0a0a0a0e0e0e0e0a0a0a0a0e0e0e0e0a0a0a0a0e0e0e0ef0f0a0a0f0f0e0e0f0f0a0a0f0f0e0e0f0f0a0a0f0f0e0e0f0f0a0a0f0f0e0ea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0e0f0f0f0e0f0f0f0e0f0f0f0ef0f0f0f0a0a0e0e0f0f0f0f0a0a0e0e0f0f0f0f0a0a0e0e0f0f0f0f0a0a0e0ef0f000e0f0f000e0f0f000e0f0f000e0f0f000e0f0f000e0f0f000e0f0f000ec0c0c0a0c0c0c0a0c0c0c0a0c0c0c0a0c0c0c0a0c0c0c0a0c0c0c0a0c0c0c0af0f0f0f0f0f04040f0f0f0f0f0f04040f0f0f0f0f0f04040f0f0f0f0f0f0404f0f0f0f000004040f0f0f0f000004040f0f0f0f000004040f0f0f0f00000404000000000000e0e0000000000000e0e0000000000000e0e0000000000000e0e501050005010500050105000501050005010500050105000501050005010500000000004040404000000000404040400000000040404040000000004040404e0e0e020e0e0e020e0e0e020e0e0e020e0e0e020e0e0e020e0e0e020e0e0e02000000005050404000000000505040400000000050504040000000005050404a0a0a0a0f0f0e0e0a0a0a0a0f0f0e0e0a0a0a0a0f0f0e0e0a0a0a0a0f0f0e0e303070203030702030307020303070203030702030307020303070203030702a0a0f0e0a0a0f0e0a0a0f0e0a0a0f0e0a0a0f0e0a0a0f0e0a0a0f0e0a0a0f0e000000000000f0e0000000000000f0e0000000000000f0e0000000000000f0e000000003030202000000000303020200000000030302020000000003030202808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080cf0f00000f0f04040f0f00000f0f04040f0f00000f0f04040f0f00000f0f0404303070703030202030307070303020203030707030302020303070703030202f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e0f0a0f0e00b000a000b000a000b000a000b000a000b000a000b000a000b000a000b000ac0c0c0c0f0f0e0e0c0c0c0c0f0f0e0e0c0c0c0c0f0f0e0e0c0c0c0c0f0f0e0e0000000000e000e00000000000e000e00000000000e000e00000000000e000ef0f0a0e0f0f0a0e0f0f0a0e0f0f0a0e0f0f0a0e0f0f0a0e0f0f0a0e0f0f0a0e504050405040504050405040504050405040504050405040504050405040504
|0,6=>0xf0f0c040f0f0c040f0f0c040f0f0c040f0f0c040f0f0c040f0f0c040f0f0c04f0f0f0f0f0f0f0f0f0f00040f0f00040f0f0f0f0f0f0f0f0f0f00040f0f0004f0f03020f0f03020f0f03020f0f03020f0f03020f0f03020f0f03020f0f0302f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000303000002020000030300000202c0c0c0c080808080c0c0c0c080808080c0c0c0c080808080c0c0c0c08080808f0f0c0c0f0f08080f0f0c0c0f0f08080f0f0c0c0f0f08080f0f0c0c0f0f0808f080f0c0f080f0c0f080f0c0f080f0c0f080f0c0f080f0c0f080f0c0f080f0cf0a03020f0a03020f0a03020f0a03020f0a03020f0a03020f0a03020f0a0302000000000000c0c0000000000000c0c0000000000000c0c0000000000000c0ce0e0e0e0e0e02020e0e0e0e0e0e02020e0e0e0e0e0e02020e0e0e0e0e0e0202e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e0e0a0e0e303030a0303030a0303030a0303030a0303030a0303030a0303030a0303030af0e0f020f0e0f020f0e0f020f0e0f020f0e0f020f0e0f020f0e0f020f0e0f02f0f080c0f0f080c0f0f080c0f0f080c0f0f080c0f0f080c0f0f080c0f0f080cf030a020f030a020f030a020f030a020f030a020f030a020f030a020f030a02f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e0f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e000050500000404000005050000040400000505000004040000050500000404a0a0f0f0a0a0e0e0a0a0f0f0a0a0e0e0a0a0f0f0a0a0e0e0a0a0f0f0a0a0e0ef040f040f040f040f040f040f040f040f040f040f040f040f040f040f040f04f0f0f0f0e0e02020f0f0f0f0e0e02020f0f0f0f0e0e02020f0f0f0f0e0e020200c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cc0c00040c0c00040c0c00040c0c00040c0c00040c0c00040c0c00040c0c00040000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0f0f0f0f0f0f0f0c0c00040c0c00040f0f0f0f0f0f0f0f0c0c00040c0c0004a0a0a0c0a0a0a0c0a0a0a0c0a0a0a0c0a0a0a0c0a0a0a0c0a0a0a0c0a0a0a0cf0f00000f0f0f0e0f0f00000f0f0f0e0f0f00000f0f0f0e0f0f00000f0f0f0e00000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0a0a030302020f0f0a0a030302020f0f0a0a030302020f0f0a0a03030202f0f0c0c0f0f04040f0f0c0c0f0f04040f0f0c0c0f0f04040f0f0c0c0f0f0404404040404040404040404040404040404040404040404040404040404040404b0b0b000b0b0b000b0b0b000b0b0b000b0b0b000b0b0b000b0b0b000b0b0b000000c0c00000e0e00000c0c00000e0e00000c0c00000e0e00000c0c00000e0e
|0,7=>0xf0f00000f0f0c0c0f0f00000f0f0c0c0f0f00000f0f0c0c0f0f00000f0f0c0c0000303000002020000030300000202000003030000020200000303000002020000a0e00000a0e00000a0e00000a0e00000a0e00000a0e00000a0e00000a0ef0a0c080f0a0c080f0a0c080f0a0c080f0a0c080f0a0c080f0a0c080f0a0c080000a0a00000e0e00000a0a00000e0e00000a0a00000e0e00000a0a00000e0ec0c0f0e0c0c0f0e0c0c0f0e0c0c0f0e0c0c0f0e0c0c0f0e0c0c0f0e0c0c0f0e00a000e000a000e000a000e000a000e000a000e000a000e000a000e000a000ec0c00000c0c04040c0c00000c0c04040c0c00000c0c04040c0c00000c0c040400c0008000c0008000c0008000c0008000c0008000c0008000c0008000c0008f0f03030a0a02020f0f03030a0a02020f0f03030a0a02020f0f03030a0a0202f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c505050504040404050505050404040405050505040404040505050504040404000030200000302000003020000030200000302000003020000030200000302f0f03030f0f02020f0f03030f0f02020f0f03030f0f02020f0f03030f0f02023020302030203020302030203020302030203020302030203020302030203024040400040404000404040004040400040404000404040004040400040404005050404050504040505040405050404050504040505040405050404050504040000f0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0c00000000e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e0000f0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0ac0c0f0f0c0c0e0e0c0c0f0f0c0c0e0e0c0c0f0f0c0c0e0e0c0c0f0f0c0c0e0e00000000f0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0c303030302020202030303030202020203030303020202020303030302020202c080c080c080c080c080c080c080c080c080c080c080c080c080c080c080c08f0f0c080f0f0c080f0f0c080f0f0c080f0f0c080f0f0c080f0f0c080f0f0c0800f000c000f000c000f000c000f000c000f000c000f000c000f000c000f000c0000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0c00000f0cf0f0f0f00000c0c0f0f0f0f00000c0c0f0f0f0f00000c0c0f0f0f0f00000c0c00000000a0a0e0e000000000a0a0e0e000000000a0a0e0e000000000a0a0e0e202020206060606020202020606060602020202060606060202020206060606f0f05050f0f04040f0f05050f0f04040f0f05050f0f04040f0f05050f0f0404
|_,_=>0
def stPool : Nat → Nat
|0=>0x50a04090708240a04030908011f050a0903041a23050a041a22160a040803091f1e050a011a091d0d050a091a1c1b050a041a190916050a0908041817050a0408011615050a04080714050409070813050409080312050a040d0c11050409080710050a0302010f0a040908070e050a040d0c0b050a09080706050403020100
|1=>0x13e0a090103081f3d05040908033c3b05030908013a39050a0908030138050a040836091605040103023534050a09041a0333050a0903041832050a091a1b0d3004090103081f2f050a040827162e050a090308042d0a04030d09012c0509080301132b050a041a0d2216050a04032a0929050a041a0d1611050a040d27160c
|2=>0x409084c0705010809034b4a050a041a0d4916050a0409084847050a0403080946050a0409080745050a04082716440a04080916074305042703210813050a0903081842050a04080d091e050a040d270c050a0408030c0b0403090813011f050a0903041a41050a0408314016050a04080216070a04030908013f050a040302
|3=>0x11050a04082a0947050a0409080357050a040802031e050a040d090c2805040103243534050a09031a0456050401031355540a04080907430a040908030153050a0408520948050a04080348400504090803515005042509260813050a040d090c20050a040803094f050a040801164e0a040d0916012c050a0408090c4d050a
|4=>0xd01091d05041a03310913050a04010d090c050a040809166405040908030163050a0409080762050a0908030161050a040d271660040908031301530409080301135f0504090803015e05040302015c5b050a091a1b0d5a050a0908041b360a040809260743050a091a1b5a0504090803015905040908030158050a0408030c
|5=>0x50a040308370971050a09030804012a050a04081a700916050a04090803486f050a04080d014916050a0908046e016d0a010809034b6c0504090803016b05090803130161050a040308096a050a040903482905040309083a69050a04011608680509080313014b05040908030167050a0401090d660a04030908012c050a08
|6=>0x179050a040903083736050a0403082a0940050a041a030922050a0408312716050a0908041b372a050a09011a0d6e1b050a0408782a0916050a091a030473180504010903132455050a040108030965050a04030d0901770a04090803240153050a040308370948050a040203160175050a040803097428050a091a03040d72
|7=>0x4732a0a04080309011f050a041a03090d22050a0403082a097f050a04080d3127160a0403090801552c0504030908130126050a042703160871050a040108091647050403091608017d050a04080901547c050a04081a09164d0a04090103081f7b050a090308047a18050a041a033109240504012509160813050a04031602
|8=>0x2013a050a09011a83036e050a04082509160c050409080301133c050a040803010285050a0403160108840504010803021354050a041a0d091620050a0904088203180504090803240158050a09080d010481050a04250908264c050a040908030176050a040916010880050a042703160848050409080313016f050a091a03
|9=>0x8010d9016050a040908037176050a091a03040d5a050a04010809168e050a091a03048d0504010803241334050a0903040d018b050a04080316018a050a040108528916050a040d012716550504090803011351050a040d09160129050a040802032120050a09080324014b0504030801370913050a091a03045a0504080316
|10=>0x308041837050a0903080472980504012703160813050a040308010997050a040831091620050a09030804019605040308012a0913050a091a030d0495050a041a030d0948050a040908037648050a040d09160160050a04080d019416050a040309080193050a090483030192050a09011a039183050a041a030d0971050a04
|11=>0xa040309200860050a04080d01099a050a041a0d091628050a091a04830318050a040308310940050a0908041b3137050a040908240199050a040108031640050a010803091d050a090408010317050a0908030138050a04090803485d050a090803240161050a09030473018f050a0108031a091d050a091a041b0d2a050a09
|12=>0x14b0504090803017d050a04030920084c050a040216550125050a04010308169f050a091a03047331050a09080473016d050a04081a031611050a04080d092826050a091a0d1b88050a040903240129050a040308092a9e050a09081b015a050a04082703160c050a04030809019c050a040809019c7c050a040809010d9b05
|13=>0x18f050a04080d019c16050409080313015d050a04080d010947050403080d09017d050a09080d01a31b050a0903040d0192050a0408032401940504010903241335050a030802014ba2050a09081b010d5a050a0903080401980504011a030d09130504090803130176050a090308010442050a0403080901a1050a08031602
|14=>0x55011f050a091a03040d18050a040309010dab050a010809034baa050a09081b010da9050a040309080120050a0908047301a7050a0401035554050a041a030d0949050a01080309521d050a0903080401a6050a090803010238050a040d09160177050a0403160108a4050a04080309201e0a04010803091653050a09041b0d
|15=>0x316016f050409080302017d050a0408091607050409080301133b050a04030d0109b1050a04030928084c050a090408b00318050a09080301a538050a091a041b0d31050a040825091674050a040803091aaf050a0904030183ad050a09011a04810d050a0403080109ac050a04081602019905040308013109130a04030908
|16=>0x90848200a04080d0916011f050a0401088fa516050a090804730117050a040309087120050a0403082a0976050a040103160849050a01080309891d050a04011a0d5416050a040908037e480504010803091658050a0908040d01b4050a04030d090175050a040203160129050a0903087301b3050a0908040d01b2050a0408
|17=>0x309010829050a04080903bcbb050a040103025554050a090401ba0373050a0903080401b90a04090103081fb8050a0904080301b7050a0408031601a5050a04090803792a050a040308780948050a0408020103b605040108031324540504010316081334050a040827030c050a0403090801b5050a04030809942a050a0403
|18=>0x40108030953050a09081b0d01b3050409080313017e050a010803091661050a0908030183bf050a0409030102be050a04080302019a050a090304016e8b050a091a04031c050a0908830103b4050a0401030d0974050a0908830103b2050a040903020175050a04080d271621050a040108031689050a0908041b782a050a04
|19=>0x403090824011f0a0403080d010953050a09088301a71b050a091a03040dc4050a0908040d01c30504030801780913050a040309084828050a090308049818050a04010d09160c050a0408030201400504030908130120050a040802032826050a0408270316c1050a04080d010989050a040916080199050a0908040d01c00a
|20=>0x907050409080301c8050a040103160890050a0403090801c70a0408030921201f050a0408091601a1050a010809034bc6050a040803091a280a0403091608012c050a04080109162e050a090304730132050a04080d0109650504030902013a5c050a04030901084c050401030d091355050a091a030430050a091a83861b0a
|21=>0xa090304010dce050a0908011c1b050a09088301171b050a030908014b050a0408032401cd050a090801bd0373050a0908031a04cc050a041a030d0997050a04270321082405040108030958050a040316080194050a0403082a09a1050a0908830301b3050a091a030d0430050a040308310976050a040803090c20050a0408
|22=>0x50a0908040d01a7050a040309080177050a098301ba031b050a09010d041ab2050a04080122160504030802013a5b0504030908130128050a04030908019a050a0403082a097e0504010903021355050a091a03047372050a030108098f380a04090803020153050403080d0109580504090803011350050a09030804187805
|23=>0x90c28050a090308730142050a040d09160175050a0108030961050a041a03090dd10a0408020316011f050a040801520954050a0408010d2216050a04080d160111050a04080926070504030908013ad00a0403090801772c050a04010d541655050a040308010940050a0409031a19050a0908041b0137050a040801785416
|24=>0x4031608019c050409080324017d050a0409082a52050a040908010347050a04010d090c050a0409160801d2050a090308010495050a09081b0d0130050a04010d091a0c050a0409080301480504090803020158050a0409030d1a19050a040803091e050a041a0d2a0916050a0903080401a3050a090408820372050a040803
|25=>0x10803021334050a090483010332050a04030d2a0979050a04080d2716260504030908130121050a090183031ab2050a04250916084c050a042509260824050a04080d014016050a04080d0901990504010316081354050a0908040d0117050a0908041b012a050a03080d010961050a040831370916050a040908240147050a
|26=>0xa09081b0d0142050a04080d092120050a090804031ad6050a040103552454050a090308047237050a09080182031b050a04030d0901d5050a0403090801d4050a04010d091674050a04011a09890d050a04030d010929050a0408031a09d3050a04080d09017c050a04080216014d050a0408091601440a04030908012c0504
|27=>0x260a0408030901161f050a042703160860050a091a0403da050a040125160854050a0403160801d9050a04081601d8050a09086e1b0137050a040d018f0916050a091a04830372050a040803020165050a0401030d0960050a090483031a70050a040903240175050a04010d091a65050401030d091335050a09080302016105
|28=>0x316084c050a09011a03736e050a040816020147050a04010803090c050a040801520924050a040803240140050a040903020129050a040903240179050a0401091608dd050a04080d2a2716050a04080309c120050a04090308360a0904080301dc050a030802014bbc050a090883010391050a041a310916050a0403090801
|29=>0x3021335050a090804010de0050a090804016ec3050a0401080916b60504090803130148050a090308040118050a090883010342050a04080d0901df050a090308040137050a040802162625050a0903040d0132050a041a0d3109160504090803130171050a04080903b6bb05040908013a03de050a0903046e018f050a0427
|30=>0x15577050a04010803091674050a0403080d2a09cb050a040108031a0989050a090308040d0118050a04081a250916050a0309041ae1050a04090803716f050409080324013a050a090304730192050a091a030472050a0409080301a5050a040308010915050a041a0d2716050a042509160848050a04080302019405040109
|31=>0x8090365050a04010803091a65050a040308310927050a0903010804e205040103080d0913050a0403090801a8050a0903080d0104b3050a04090308012a050a040108030916c1050a04080203160120050a0908041b0d0131050a09030804730198050a090403010892050a040102031655050a040108030989050a04030908
|32=>0x901031f050a0901031a520483050a04030908240121050a09030804730178050a04010316082454050a0403080d310927050a04030809019d050a091a04830386050a090408830103a7050a0409010308ab050a0401080903bcb6050a09088301b0031b050a041a030d09cb050a09081a0304e3050a0403080201bc050a0401
|33=>0xa0403091608017e050a04080203160128050a09040803011c050a09040883010317050a04081a270316050a04010803095289050a040308010994050a0403010908be050a0403080109900504010908030213050a040108030976050a0403080d09019d050a040825091626050a040309010875050a040908030102a50a0408
|34=>0x50a09088301861b050a09030804010dc4050a0409080103e6050a040803160111050a04080309011620050a09030804016ea3050a04012509160855050a04030802016fbc050a0403080d010994050a0401080d5416050a0904080103a7050a0903080401c4050a04030809010d90050a0408270321050a0403080d01097605
|35=>0x3240171050a040908010399050a090108040317050a0401081a520916050a0904080301ea050a0408c2270316050a0401080309c1050a0903010408ad050a090108bd031b050a090801e8031b050a040308010997050a0904010803bab9050a0908041b0d0178050a09040883010398050a040108030974050a090308010430
|36=>0x2a050a04081a03091620050a04030809019c050401030916082413050a04080d09160126050a090108040391050a04090803240148050a0403080d010997050a04030801370954050a04080203160121050a040827031626050a090108041a0391050a0903080d010430050a04090803020176050a040108520916050a040908
|37=>0x8250926050a0403080901d1050a040309080155a8050a04012703160855050a040803092120050a04030916010829050a090108040398050a04080d01370916050a0403080201cd050a090108030442050a0403080901a1050a040301080985050a040108032454050a09030804730172050a09081a0403ed050a0409030837
|38=>0x901549d050a0901041aec030d050a04090802010399050a090308046e0137050a0904080103f1050a04030916010860050a0408031601f0050a04090803017e050a04030809010dd1050a0403090801ef050a090308040d0198050a0904010308ce050a0903080d010442050a04030809010da1050a0403080d09019c050a04
|39=>0x954050a04081a03091628050a0904010803e0050a0401030d0955050a0409080324016f050a0409080301f2050a0403091601084c050a090408030183b7050a04030908240126050a0403080d09017e050a040803090120050a04080d012a0916050a0408c203091620050a04012509160824050a0901041b08ee050a040308
|40=>0x302017e050a04030d0901790504010908032413050a090308040d018c050a040903083137050a04091a030d2a050a09081a88031b050a04030801370924050a04030801092a97050a09048303018f050a09030804018c050a04011a0d0916050a04030108098fa5050a0401086f0316050a04010803022454050a04011a030d
|41=>0x901080403ec91050a0903080473017a050a0904080103da050a040308012a09240504030908013a050a040109030255050a09081a0403f4050a09040883030172050a0903080401b9050a0904080301b7050a0401080309169a050a04081a0309200a040803091601201f050a09011a03046e050a0409080d0152050a040908
|42=>0x1310916050a0408031602016f050a04081a0903e4050a04030916080171050a09040801820373050a04080203160126050a09030804010db9050a0908c288031b050a0401091abc030d050a09011a03040d6e050a040801310916050a0403091608017705040103080d092413050a04012703160824050a040901030829050a
|43=>0xa0403080901f6050a0908c20304f4050a04080d012716050a0408c2090320050a0904080301f5050a0403080901549c050a040908030187050a0409030d018f050a04030916080148050a040309020179050a090108030481050a0401088f0916050a0901088303736e050a040309010860050a090108031a0481050a04080d
|44=>0xd0172050a0409080324015d050403090802013a050a0409080d016d050a090301040832050a04081a030928050a090408030183ae050a040103160854050401090803022413050a040803092026050a0409080103dd050a04011a030d0924050a04090803240176050a04030901084c050a04091a0331050a09030804017205
|45=>0x30908550120050a030108094b050a09010308736e050a09030804730118050a040901080379a1050a09081a86041b050a09081a0403d7050a09011a0403eb050a09030804730137050a0401080903b6050a0904080301f7050a040108091a03b6050a0409080d013752050a0401031608a0050a04091a030d31050a09030804
|46=>0x4090108039b050a0904088303017a050a0904080301ae050a0403090108264c050a0309088301ec050a0309048301ba050a04090803010287050a04030801780954050a040908031a70050a04010809039a050a09010803045281050a04030801310924050a09011a04830373050a0403010809f8050a040308090122050a04
|47=>0x15a050a0908c286041b050a04081a0309e5050a04090308782a050a04080d09160120050a09081a0304e9050a040108030940050a0401080309160c050a040803092826050a09010837041b050a040802160125050a04010d091655050a040309080177050a0903080473012a050a040801780916050a04030809010d22050a
|48=>0x81a09034d050a09011a030473050a090308010495050a0403080d010940050a040908030148050a04030809017f050a0908041b0d0137050a0903080401a3050a0908830182031b050a0409011a520d050a030908830182ec050a0409080301f9050a091a030d0488050a04080d01780916050a040908030171050a09030804
|49=>0xa04030809010d7f050a091a030d04c5050a090308040d01a3050a0908041b012a050a0403080d090171050a03090802014b050a04030908550128050a09030804010d5a0504010309160813050a0408031602015d050a090108f3031b050a09030804018d050a04081a030911050a040108090347050a0901080d6e1b050a04
|50=>0x30d0401ba050a09040801b00373050a09030804016e8c050a04010803091665050a0409080324017e050a0908041b0d012a050a040309160801a8050a0904010803fa050a0903080401cf050a0903080401a9050a09011a03040d73050a0903080d010495050a090308046e0178050a0403080d090148050a09030804017a05
|51=>0xa091a04830325050a0409080301d8050a09010804031ab2050a0309088301bd050a09010883036e050a09010882031b050a04080d09160128050a09030804010dcf050a09040883030118050a09030804010da9050a040109032455050a0403082a0927050a030904080182050a090308040d017a050a0901086d041b050a09
|52=>0x1f050a09030804730131050a04090803020148050a0401030d092455050a03091a04db050a0409010803fc050a0403080d2a0927050a09080d1b0188050a09011a0d041b050a04030801780924050a0903010804bf050a04090803020171050a0409080301fb050a0901080304b4050a0901080304b2050a0403090824012005
|53=>0x80137050a041a030d0927050a0409080301ca050a09030108048fb7050a040308010949050a0904080301fd050a040108030254050a04010803090c050a04010803091a0c050a04030908016f050a03090802016f4b050a04010803091676050a04090802010347050a040803090126050a040309160108750a040803091601
|54=>0x50a0403090824012805040109080313050a09011a83031b050a0309011aec83050a04010903022455050a04080916014d050a0903080104b3050a0409080301a5050a0403080d010949050a040108cd0316050a04080d09160121050a0403082a09cb050a090308040118050a040827031621050a09081a0403fe050a040903
|55=>0x50a0409011a030d050a040103080954050a040103090855050a04010309160824050a04090108036d050a040903080d012a050a0309010804ec050a0403090802016f050a0901081a04031b050a030904088301b0050a03090108041aec050a040801270316050a04090308012a050a09030801042a95050a04090308010d37
|56=>0x80d0131050a0403010809bc050a0309010804bd050a09010308046e050a0309040801e8050a040903080131050a04030108091abc050a0908040103ed050a04080309160120050a0401080d0916050a040309010879050a04030908015d050a0309040801b0050a040103080d0954050a090108c204031b050a0403090108a0
|57=>0x309160121050a040903080178050a09010408830373050a0908030104f4050a040809010320050a0901040803eb050a0903080d040188050a0401090803c9050a09080188031b050a040103080d0924050a04080309160128050a040109080324050a0403090802015d050a04090301088f050a09010308040d6e050a040903
|58=>0x50a030908c20488050a0309040108ba050a040803090128050a0309040801db050a090103080473050a0309081a04c5050a09040883030125050a0403010809cd050a0403090801e7050a0408090103e4050a040903080d0178050a040108020316050a0309081a0488050a0903080d0401c5050a04010908030224050a0408
|59=>0x30916050a09040883030186050a040803010911050a04080901034d050a0403080d0901cb050a0408030109e5050a0908030104e9050a0403081a0927050a0901080d041b050a040803090121050a0409030108ee050a0401081a030916050a0403080d090127050a09080186041b050a0908040301d7050a09010308040d73
|60=>0x90802030186050a040801250916050a04010309160855050a0409081a0386050a030901080482050a0403090801f0050a0908040103fe050a0309040108f3050a03090408830182050a0403081a09cb050a040308c20927050a09010883031b050a04080309160126050a04090802030125050a0409081a0325050a040108c2
|61=>0x901cb050a040108030916050a040908030125050a040308090127050a0309080401c5050a030908040188050a09010804031b050a040903080d0137050a0309011a0483050a040908c20386050a040901080337050a0908030104e3050a040901080352050a04030108096f050a04090108031a52050a040803090126050a04
|62=>0x50a0403090108050a040301090802050a0403090108c2050a04090103080d050a04030901081a050a040908030186050a030901040883050a040308
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x6cc030601530091803cc018600930031800cc0006
|6,0=>0xf8b87a9c3c6e1dc70eab8739c390c1c170dd386cdc358e1a570cf3865dc320e18970c1385edc2e8e16d70b33857dc2b0e15170a53850dc278e1357097b04a1c242e11a7089b8431c20ae0fe707bb83c1c1d2e0e2706db8351c19ae0c6705fb82e1c162e0aa7051b8271c12ae08e7043b8201c0f2e0727035b819580bce0577028b0129c086e03c7
|6,1=>0xb25c584e2bb715a38ab5c54ce29f714c38a45c514e283713e389d5c4dce267713038965c4a4e24b7122388f5c46ce22f711438885c434e2146106b8819c3fee1f87
|7,0=>0x262412f2096904ac8252412720929048c8242b91f608eb046d8232c117608ab044d8222c10f6086b042d8212c1076082b040d8202c0ff607ece3ee81f340f7a07ad03ce81e340efa076d03ae81d340e7a072d038e81c340dfa06ed036e81b3b8d81c6b1035081a440d0206710330819440c8206310310818440c0205f102f0817440b8205b102d08
|7,1=>0x35f41ada0d5d06a6834f41a5a0d1d0686833f419ddccdf0667832fc195e0c9f0647831fc18e1cc6106288310b98660c2306098300c17e60be305e982f0c17660ba305c982e0c16e9cb6505ab72d1c166e0b27058b82c1c15ee0ae7056b82b1c156e0aa7054b82a1c14ee0a67052b8291c146e0a27050b8281c13ee09e704eb8271c1371c9a904cc8
|7,2=>0x45dc22ce115708a3844dc2251d1190884843e421d210d90864842e4215210990844841e420d210590824840e420521019080483fe41fd20fdae7e583eec1f560f9b07c583dec1ed60f5b07a583cec1e560f1b078583bec1dd60edb076583aec1d560e9b0746739f41cda0e5d0726838f41c5a0e1d0706837f41bda0ddd06e6836f41b5a0d9d06c68
|7,3=>0x55a3aab215490a9c854a42a3215090a7e653bba9be14cf0a5f852bc293e148f0a3f851bc28be144f0a1f850bc283e1410ea0174fcc27c613d309e184ecc2746139309c184dcc26c6135309a184ccc26461313098184bd3a5ca12d5096284ad4254a12950942849dba4ce12570923848dc244e12170903847dc23ce11d708e3846dc234e119708c38
|7,4=>0x6554328a19350c9286454320a18f50c728635bb18e18b8ec5486264311218790c34861643092183aec158606c301617fb0bf585f6c2f99d7bd0bd685e742f1a177d0bb775d7c2e9e173f0b9785c83ae2217010b7885b842da216c10b5975a8c2d2616830b398598c2ca616430b198588c2c2616030af985793abaa15c6eadb8569c2b2e15870abb8
|7,5=>0x75243a721d290e8c8742439f21ce90e6c8732439721ca90e4c8722438f21c690e2c8712bb879dc2d0e0e8703bb7fe1bef0def86f43b7821bb10dd176e4c37061b730db186d4c36861b330d9186c4c36061af30d7186b4c35861ab30d5186a4c35061a730d318694c34861a330d118684c3409d9f50cf286754338a19b50cd286654330a19750cb28
|7,6=>0xf4a77a143cea1e650f2b7791c3c6e1e28ef0c878243bf21de90eec877243b721da90ecc876243af21d690eac8
|8,0=>0x8b3c457e22ad314d98a24c4ee6265312a88914446a2223310a7880cc3e261df30e7886f4c35a219b30c5885ec42d6215b10a5884e4c25221191083983e3c1ce60d53061982c4c13e608f103f881b4c0ba204b301c980a4403220090ffc87f9cbfae1fc70fdb87e9c3f2a5f850fb997d84be9e5f3d2f9687c743e1a1efb2f7497b5cbd8a5eb32f518
|8,1=>0x9c2c4df266e7336a99b0ccd6626a1334889a044cde665f1326998f44c5666193303997e3cbd225d732e2996d44b46659312c0995c44ac2255112a0894c44a3e650f127f893b4c9ba24cb325c992a4492e6485323999184c8a2243f32169906cc81623f931f488f64478e63b711d388e5c470e237711b388d5c468a6333319098c44460222f1116f9
|8,2=>0xad3c567e2b2d358e8ac2cd5f26ae7356b8ab14d5666aa135479a9fc54da6a5b35258a8e4d44e6a1535028a7ccd3c269d114df9a6c3d342299114bf9a5bc52be294d349e8a4acd236290b147c9a3a451b228c7345b8a29c512e288534399a18c50a6284314189a084501e67fd33f599f6c4f9627b933d489e5ccf0a677333b099d444e7e672d338d9
|8,3=>0xbde45ed22f5917a48bce45e4e6f1717829bbd45dc66ed317609bac45d422e8f373e9b9b45cba2e4b371c9b89cdc2e2e0716fa9b79bdbae2dc536d99b68c5b262d8316b89b5845aa22d3f36969b4745a1a2cfb36749b36459922cb916548b25cd90e2c7536328b15458866c3136108b04bd8062bf315f18af4c57862bb315d09ae4457022b6f35af8
|8,4=>0xcec46742338f39be9cdace6b27349199c8cca4662e7307197b8cb94e5a672c139579ca74e516727b19358c96c6492723739129c84ce40631f138f08c73ce37e31ad38ce8c62ce2f2716918ab9c51c626e3127188b8c41c61ee30e7186b8c314e16a30a518499c20c60e2706118279c0fc605e301d38068bff45fda2fdd17e68beecdf562f9b17c49
|8,5=>0xdc4cee0276ef3b707db446d8236af3b4f8da3c6cfe366d3b2e8d92cec76362b1b0d8d82c6bf635eb1aed8d724eb7235a91acc8d6246aee75671aaa9d50cea6275211a879d3fc69da74db3a649d2ebe95634993a448d1e468ce74571a229d0d4684a34151a019cfcc67c633d139e08
|9,0=>0xed14f6667b231d898ec04f5e23ae11d688eb0475623aa11d479e9fc74de3a5f1d269e8f4745a3a1b3d049e7dcf3ce39d53ce28e6d4734a39933cc18e5cc72c2794f3c9f8e4b4f23a390b3c7c9e3a471b238c91c5c8e2a4712e78871c3a9e19470aa38451c1a8e08cf02278011bf88df846fa237bf3bd78de74ef1a377b3bb49dd5cee8a77351b928
|9,1=>0x7b127d791eb48f5647a923d391e948f45cfa0e3cf53e728f34cf9863cb31e518f24c79063c713e308f14478823c2f3e0e9f03477f67be93dec8ef24776e7ba71dcb8ee1c76ee3b671dab8
|10,0=>0x1f2d8f92c7c763e2b1f0d8f82c7bf63deb1eed8f72c7b763dab1ecd8
|11,0=>0x1f357
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 255 then fld (dictB (i / 512) (i / 32 % 16)) 252 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 8 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 17 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x931434040308404210807498951601c0c2503018349b1601c0c25090140c210507898951601c0c25030188087160145804030940c21161a00c25090140c2101084989503018580703094242103094dcc70d014340403084244e081382892030242421043143404040340c210108424a1160180c250308404211608498951601c0c25030188087052085805160100c25
|1=>0xd09434050308420a1160180c2509085cc04040d40c21010840c251a25c0c060108408052401c0c09090840c25093143404030846997161a80c250308404210807898951601c0c25030188421160100c25090140c213a094e8210a5d4080609084dcc70d0143404040340c210507898951601c0c250301880871601458040309424210507898951601c0c25030180c25
|2=>0x160840c2509015d80f161a40c250108429f9240185821030940ca1160180c2501084207e052080c9d0901434250d0100c21010842892160840c2503018dcc70d014340403084349c090140c21010840c250901434040308434070d014100d03084100d040d80c21010840c250d01c340603085cc07040d40c210108490230a2480c090908415da240140c09090849007
|3=>0x83034102101084261d8602c0c050908425812108458040309490270a2480c09090845805030940c2101085cc07830360c050408429da240140c090908420991601c0c250301891f9240180c09090840d31082645807030949007160840c250901408050a2480c09090843407040d40c2101084349e090143407030840c250901434040308458070a2485821030949004
|4=>0x1601858230309421e97301a0c0d0408490040d0940c21010840c250d27c2405030845a3f0309420950301805b8040d80c2101084244e0a2480c09090863021016ec1036030840887160100c25090840c25095240c6a010845823030942405030848023160140c25030845805160100c250908411be020140c09090862034040140c21010842975020180c2509085cc13
|5=>0xd010100d030840df9240180c0909085d827161a40c25010841226095240c6a0108411da240140c090908421e10d0181035030841226095240c6a010843407040340c210108434057301c1035030842892160840c250901458050309434040308410a90d01c0c210108490070d0940c21010849007240140c09090848421160100c25030840c250978434060308554a1
|6=>0x20140c25090845a832708c0c25090140de10d01810350308424a1160180c25010845807160180c25030841005040340c2101085d823240140c0909086203404014100d0308458680309424050108675510154c3427030840e72015443427030840dfd0d278240503084842116014580403095b425037843406030845806030940c2101085cc07830341021010843405
|7=>0x826458070309480871601458040309415da161a40c250108421e10d018100d030840c250154434270308408060a2480c0909085d80f3709434050308429f924018342503084100d016e410360308421e97301810350308425f9240180c0909084204e0a2480c0909084252e046f808050908428920d0940c210108490050a2480c090908435f92401834250308411be
|8=>0x22540c06090843404040340c210108468a3160180c250108422b9838680c050408490c70d0943404030840d75020180c250908428920d094340403085cc07040d40c210108421fd0d2782405030840d2e046f8246901086203604014100d030845aa10155c5823030940de97301810350308490272408c0c090908424c50d0100c21010841296022540c06090842532
|9=>0x7301410350308458052401058210309490050d094340703084909c160840c25090141226095240c6a010840c250d09c0c210108429da161a40c25010846de10d018100d0308421f9240183425030848023160140c250908411e9730181035030846cde0d014100d030840975020180c250908429f9240180c090908498951601c0c250301a5c23092a43407030841296
|10=>0xd0940c2101084105e8203e0c050408421f9240180c09090845804030942405030842595161a80c250108434070d018100d0308490272408c0c09090860c0d08b060c0604084207d052080c9d0901408a1160180c250908490270a2480c0909084244e0a24858210309458680309424050108458052401c5821030941482160140c25030840c25098f420950301a600f
|11=>0x730141035030845868030940c2101085d827240140c090908458050a2485821030945807160180c25090845b0b0309424050108c0df9240185821030940e8e016e410360308411e10d018100d0308411da161a40c250108412b9838680c0504084221d8602c0c05090845975020180c25090863021016ec1036030860e1803014102101086f40d04b060c0604084906b
|12=>0x1601458040309434a1160180c25030840d2d046f824690108415de0155458230309458c7030943404030866023730141035030840d023709c340503084e8210a5d408060908490230a24834250308410c50d0100c2101084100d0301410210108414821601458210309415da37094340503084100d03b060c06040843717040180c21010840e31016ec103603085cc07
|13=>0x880dc100503084100d838600c0504084100d8203e0c05040842575020180c09090860c0d04b060c060408411c11a25c0c06010845821160100c250901425f924018582103094372d0901834070308411e97301a0c0d0408410c50d0100c21010845805161a00c250108498951601c0c25030182b2901c9c0c0a09084909f160840c25090148157160145823030941482
|14=>0x1601c0c2503018e8090a5d408060908415de0155458230309458230309434270308468c70d0100c210108435e10d018100d030840de973018103503086a1550155c582303094100d08b060c06040846c6a040340c21010840c250d270240503084e8250a5d408060908490230a2480c090908415da240140c090908429da37094340503084044d0a2480c0909084233d
|15=>0x240180c0909084dc0f0d01c3405030845868030940c21010840ea10155c58230309410c50d010100d030845868030940c210108429da240140c090908468c70d0100c21010848087160145804030940c250d01c0c2101085cc04830360c05040843006161a00c250108660137301410350308420a1160180c25030841482160140c250908424a1160180c25030849895
|16=>0x820360c0504084232d0901834070308458070309424050308458040a2485821030946c6a0403410210108420991601c0c250301858211601c0c25030180c253709c3405030840df92401834250308490270a248582103096600f7301410350308434c70d010100d0308411da370943405030840c250d014340403085d80f240140c090908405512409c58210309429f9
|17=>0xa24834250308411da240140c090908410de0d014100d030845805160100c25030846b5f1b018100d0108490272408c0c0909084340573010103503084100d83b060c060408674210154c342703084586b030940c2101085d823370943405030840e72015443427030840ca1160180c2509084349b1601c0c250308415de01554582303094244e0a2480c09090866023
|18=>0x46f80805090840c250d0100c210108459c7240105821030941482162845806030948421160100c25090140f6d8301010210108426a10155c5823030940897030180c25090843405040341036030840c2508784340603085cc048303410210108459be020140c250908490680d0940c210108468970301810210108421f9240180c0909084586a030940c2101084204e
|19=>0x730141035030840c250d0100c2101086d80703bc4246a01084e80d0a5d408060908420991601c0c2509015cc13040d40c21010840dbe020140c25090846997161a80c250108434253703c340503085d827240140c0909085d823240140c09090842175020180c09090849097160840c25030180c2509014340703084070516c2c0c250108cdcc70d014340403085bc27
|20=>0x1085cc07040d40c21030940c06010846b6f830101021010840805240100c090908421e973018103503085cc04040d40c210108409f9240180c09090840c25090140c21010849007160840c250301825f9240180c0909084204e0a2480c09090840f3d880dc1005030840d95161a80c25010866013820360c05040840e750154c3427030840c061601c0c25090866023
|21=>0x30840421042540c0601085bc2702014242103bc8246a01084586a03094042109014340403084123e082540c060a24834250308405571608c0c250478434060308434c70d0100c2116c2c0c250108c58050309424210d010100d03085cc05040d40c2108d746c06040345823030942421095240c6a0108405551608c0c25161ac0c250108424060d01c0c21095240c6a
|22=>0x978434060308423958609c0c05092a83407030842892030242421161a40c250108405530d09c0c211601c0c250301820a1160180c25022540c06090841482032742405040840c6a010845804160840c250d0181035030849027160840c250901434040308405530d09c0c21030141021010840ec183018102108e440c9e090140ef1091a80421040360c06040842406
|23=>0x3084100d0301410210dc5c1006030840f9d0201024210928458060309458a1160180c25016e41036030845823030940c066f09c08050908425e10d0180c21030943427030840ec18301810210dc5c100603084349f090140c21160100c2509014dc250d0140c21240185821030945806030942421838600c0504086080f830141021030942405010842549031a80421
|24=>0x309424211601c0c25090140fb1041a80421043143404030849005030242421030940c6a010849004030242421035d4080609086080f041a40421030940c6a0108407ad8303c10210309424050108c5b0b03094042308e94121a03014100d04c240423040360c070408424a90d01c0c2103ba42315040183406040340c21820360c0504084586b030940421043143404
|25=>0x1608c0c25090145805160100c252008c5805030946c69040340421030943405030842575020182421043780c6901084372d090180c2109ee6182303014902703024242173010103503086200f0401404210d01c3405030845805030940421015443427030842892160840c251601c0c25030840fb1041a804212401c0c090908424a90d01c0c210d09c3405030845804
|26=>0x30845805030940423160840c250301a1823040340c050154c3427030840c21041a80421035d40806090843405040d80c2103e860c07040848421160100c250201c0c250908490060302424210dcbc24060308405541608c0c257301410350308423b58803c100504378340503084372d090180c21015443427030845807030940c060dcbc24060308405571608c0c25
|27=>0x308404210403410050108434250d0140c21092a43407030842095030181021016ec1036030840c25030840421098f42095030180c25091a404212409c0c09090843427030840421160180c25010840fcd8808c10052408c3425030840805030242421860280c050908420991601c0c25832540c06040845807160840c252401834250308458a1160180c25030943407
|28=>0x2008c0c9d090140fb1041a80421730181035030840f6d8301010210d09434070308429750201824212408c0c09090846c05040340421730120c0d040843715040180c21832540c06040845b09030940423160140c25010841482160140c25040d80c2101084dc0f0d0140c21240180c0909084232d090180c210a2480c090908405bb040d80c210d0143404030843407
|29=>0x30849007160840c25085d40806090841149031a8042103094209503019cc13830341021210845804030941149031a80421030943404030840805030942421032782405010849004160840c25830360c050408458070309424210dc54100603084100d04014042303084246a0108410360308404210309434040308405551608c0c250a2483425030845821030942405
|30=>0x2018242103784340603087d023048640c05160180c25010860e1a0301410212409c58210309428920302424211601c5805030940fc10201c24210d0940c210108490050302424210826458070309434040308404217301010350308405500d09c0c21048640c050108c0c25090140c210327424050108e0c9703018102101544342703086180b030142421087843406
|31=>0xd0943404030860c0d040840421098f8209503018349c090140c211601458230309411be091a404217304c103503085cc07040d40c2103794232d09018100d0301404211b018100d010860c0f0408404210d0141035030840ef1091a8042101ebe0c0f040840ef1091a804213703c3405030849c230309424050d0100c2101085cc04040d40c21020180c09090842975
|32=>0x1084dc27031a40421161a00c25010845807160180c25040340c69010840c060309424211608c0c250308405551608c0c250d01c1035030840c250d0180c210d2702405030840e812708c24057301a0c0d040860e1a03014102108264580703096081383014102108b060c0604086180b0301424210d09c340603084689703018042103cd427090108c1149031a80421
|33=>0x40d80c2103cb42406010841035030840421042a4340703084dc270d0140c212401c0c0909084349e090140c210d014100d0308405b9040d80c21040360c05040840c21031a804218204e0c05040840725030282421040140c21010840c250d0180c21240100c09090862034040140c21040340c050108e18270301404210d01c3406030845805030940c21048680c05
|34=>0x3ba823150401a2037040140c21016e81036030841035030840421042a434070308490070d0940c2173018103503084349e090140c21040180c210108405b9040d80c210d01c100d0308490040d0940c21046f808050908458061608c0c25880d01005030842892160840c25020180c2509084100d8808c1005016e01036030842495030180421036f8246901084100d
|35=>0x108408970301824211b1a8100d0108412c18301810217304e0c0d04084100d041a40421160180c25030862037040140c217301e0c0d040862036040140c212408c0c090908424050d01c0c2183b060c0604085cc06040d40c21040340f090108c2315040180c21830360c060408405bb040d80c21161a80c250108490060302424210d01c100d0308405571608c0c25
|36=>0x20142421161a40c25010840dbe0201424211621c58040309420a1160180c25052085805030943404040d40c212401c0c090908490230d0940c21830101021010840de608cb42406090143407030841005040340c21040340c210108434250d0180c2104ee61823030149004030242421860200c050908411b503c240423045280c6a010845805160840c25030181021
|37=>0x2408c0c09090840ca1160180c25047843406030840895030182421093143404030840c2509c240423160100c250308424060d01c0c217301c103503084580403094240503c5410060108435e10d0180c21090140c21010840727030282421048f420950301824c50d0100c218386c0c05040849027030242421161a00c25010845868030940421025d408060908411be
|38=>0x91a804218803c1005160140c25030940c2108cb424060201824218301810210d09c0c210403404232708c24050308404210d09c0c211608c0c25160840c2503c2404230d01c0c21041a80421020142421040340421830181021041a804210309424050d01c0c21042a434070308435e10d0180c21160185821030942892030242421040341021010841021041a80421
|39=>0x40d40c2104018042103018102109c2404230201024210327824050d0180c21030942421040140421040180c21030242421160100c250d0180c21830341021048640c050327424058303c1021040140c210302824210403410050d0940c21160180c25030242421020182421082540c06040d80c210d0100c21091a8042104c240423040d80c218301c10210d0100c21
|40=>0x30140421041a404210201c242103c5410068808c10058301410210901804210901404230403410211601c0c25030182421030180421030940423030141021092540c0603cb42406090180c218609c0c05048680c05090140421040340c21160100c258608c0c05030940421090140c21040340c051b018100d040d40c2104014042308c541006160180c25830101021
|41=>0x24210108c0c21010840c05040842406030940c0609014100604014100d0d0140c21040840421030140423031a40421042540c06031a80421091a40421031a804211601c0c25030142421030940c061608c0c25
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x4650000000000000000041500000000000000000000000000000000000000000000000003c5000000000375032502d50000000002850235000000000000000001e5000000000000000000000000019501450000000000f5000000000000000000000000000000a500000055000000000000000500000000000000000000
|6,1=>0x6450000000005f5000005a500000000000005550000050504b500000000000000000000
|7,0=>0x11d4119411540000111410d410940000105410140fd4000000000f940f540f140ed40e940e5400000e140dd40d940d540d140cd4000000000c940c5400000c140bd40b940b5400000b140ad400000a940a5400000a14000009d409940954091408d40894085400000000081407d407940000075400000000071406d406940000
|7,1=>0x1d141cd4000000001c941c5400001c141bd40000000000001b9400001b541b141ad41a941a5400001a1419d419941954191418d4189418541814000017d417941754171400000000000016d416941654161415d4000015940000155400000000151414d414941454141413d413940000135413140000000012d4129412541214
|7,2=>0x2954291428d40000000028942854281427d427942754271426d4269400002654261425d425942554251424d424942454000024140000000023d42394000023542314000022d4229422540000221421d421942154211420d42094205400000000201400001fd41f941f541f141ed41e941e541e141dd41d941d54
|7,3=>0x361435d4359435540000351434d434943454341433d4339433540000331432d4329432543214000031d431943154311430d4309430543014000000002fd42f942f542f142ed42e9400002e542e1400002dd400002d942d542d142cd42c942c542c142bd42b942b542b142ad42a94000000002a542a14000029d400002994
|7,4=>0x41944154411440d44094405440143fd43f9400003f543f1400003ed43e9400003e543e143dd43d9400003d543d143cd43c94000000003c54000000003c143bd43b943b543b1400003ad43a9400003a543a1439d439943954391400000000000038d400000000389438543814000037d4379437540000371436d4369400003654
|7,5=>0x4f9400004f544f1400004ed44e944e544e144dd44d944d544d144cd44c944c544c1400004bd400004b944b544b144ad44a9400004a544a1449d449944954491448d448944854481447d447944754471446d446944654461445d400004594000045540000451444d444944454441443d443944354431442d442944254421441d4
|7,6=>0x53545314000052d4529452540000521451d4519451545114000050d40000000050945054000050144fd4
|8,0=>0x5f635f335f035ed35ea35e735e435e135de35db35d835d535d235cf35cc35c935c635c335c035bd35ba35b735b435b135ae35ab35a835a535a2359f359c3599359635933590358d358a358735843581357e357b357835753572356f356c3569356635633560355d355a355735543551354e354b354835453542353f353c35393
|8,1=>0x6b636b336b036ad36aa36a736a436a1369e369b369836953692368f368c3689368636833680367d367a367736743671366e366b366836653662365f365c3659365636533650364d364a364736443641363e363b363836353632362f362c3629362636233620361d361a361736143611360e360b36083605360235ff35fc35f93
|8,2=>0x77637733770376d376a376737643761375e375b375837553752374f374c3749374637433740373d373a373737343731372e372b372837253722371f371c3719371637133710370d370a37073704370136fe36fb36f836f536f236ef36ec36e936e636e336e036dd36da36d736d436d136ce36cb36c836c536c236bf36bc36b93
|8,3=>0x83638333830382d382a382738243821381e381b381838153812380f380c380938063803380037fd37fa37f737f437f137ee37eb37e837e537e237df37dc37d937d637d337d037cd37ca37c737c437c137be37bb37b837b537b237af37ac37a937a637a337a0379d379a379737943791378e378b378837853782377f377c37793
|8,4=>0x8f338f038ed38ea38e738e438e138de38db38d838d538d238cf38cc38c938c638c338c038bd38ba38b738b438b1300008ae38ab38a838a538a2389f389c3899389638933890388d388a388738843881387e387b387838753872386f386c3869386638633860385d385a385738543851384e384b384838453842383f383c38393
|8,5=>0x98f398c3989398639833980397d397a397739743971396e396b396839653962395f395c3959395639533950394d394a394739443941393e393b393839353932392f392c3929392639233920391d391a391739143911390e390b39083905390238ff38fc38f938f63
|9,0=>0xa102a0e2a0c2a0a2a082a062a042a022a0029fe29fc29fa29f829f629f429f229f029ee29ec29ea29e829e629e429e229e029de29dc29da29d829d629d429d229d029ce29cc29ca29c829c629c429c229c029be29bc29ba29b829b629b429b229b029ae29ac29aa29a829a629a429a229a0299e299c299a29982996299429922
|9,1=>0xa562a542a522a502a4e2a4c2a4a2a482a462a442a422a402a3e2a3c2a3a2a382a362a342a322a302a2e2a2c2a2a2a282a262a242a222a202a1e2a1c2a1a2a182a162a142a122
|10,0=>0xa641a631a621a611a601a5f1a5e1a5d1a5c1a5b1a5a1a591a581
|11,0=>0xa650
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 16 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|6,0=>0x8000000000000001000000000c0000000000000000005000000001000800000000000000000000000000000000040000000000000000000010050000000000000000000000000000000000000000000000000000000000000800000000000047800100402000000000000008000080000000000000000000000100000000000000000000000000000000080001000000000000040000000000000000000000000000000000008200000000008000000000000000004000000000000000000000000
|7,0=>0x802040100000000000002000208000000008000280000000000000000120000000030000100001000c0400008000000708000200004000080200a0004000220001000080000000002000410001200010000000000000000000400300000440200000040000000100000008040000000000400800010000008000c000900001800028000000010044000000000000001000390000080050000200020200000000000008000400000800000036c000502400000000000000014000a004050402c00004000080000000080020c00060004000100100000000000000000800040000000008000280002400040000000020000100000000010001000000900000000003280435c1000200000000800100020080000000000000400008000400000000800000000000028000004000600000
|7,1=>0x2400040000540040000000004020af0003000040000200008000180004c00000000800090000040002000090000000014807980b8200002000100008000400008800000000000001000080001400090001000020000000004a000400000000800000000080000a000140002000400026a000100008000040000a000300044800040000000000020a0005000000002140000000940000000000000000401000220065800000000000022000300840000010002000020000a0002040000000000004000040008a000100020800040012000012105f80000400200000000000002000048000000020000050000000020000800010000000010000028001008200000480020800810001000000000000004000010004018050000800400800200008001050000880080000280041
|7,2=>0x400100000000040001000000000400400000100022800020000080005000a2000300028030040400e00000008280000003f600120000400014201e600000002a020870800001100000800004000301000800208010000822000100010000080008c01004000200010000b0000000088000000020a00001000202008000300004000028000500080004000008003000000800004000400045000120001400100000400008000040004000010000400000008e8004c0000000090008800000000080005010558014000000000100002000010008800000000000014000000000002200018f0010000008000200000200260008000000000500004008000180001070000a000000000000000080a0000000000000400008002080000000050060800040000000051000a000010000000001
|7,3=>0x100a100008000000020800f1001000000000c9800040000a0002400028000000012000000000000050008800000000200005
|8,0=>0x470e8010081a20001408008006fe0226024f3001be00140006f840040837e0019090202004c0039e003de00204001c061f60c13000df8204c0290e0067c9073820b70090e0091020db82113062bc802fc0206c001c2037e00105002601000000b80076c909a2002404106006fc0020800f70037e00570045d810d7001fe086fc205b80bbf0036e480400012020040033e003dc15d380050001ef043ec00ad20040800a8052140026200af001fe0039c0882010db0230e00024000a001ff000a80075c80c4000ff0437e0067c025b80197400990035c007f910c00037e40d100008800608081a04440006f809b700028046fc808800810209b6503dc82479009b002080437c8059804bf001be0009000bf800500602c000d00020000ff0093e4067e002100118000a0446500132001ff
|8,1=>0x801f6006fc026fc00978017e10010007f801040216e00010107b8010c2114e0231c008200004202ae0c2dc809000051014204026c00fbc0012003be02a1c012212010007fe003dc1449800642036e003dc808e321050236ec05bc013200051009a68801c00df800df00209802bc020a8319b0036e010640061801bf203be00bdc006f801f70232e0075c007fa0048041be8015c0026004c72037e013fc0502800ff28268801700a480119f000b800150000e120400856e404710012000ff8609c01034020a801bf2022000100007f81001101be0125c00db80a50241de5037c182000197062a4902dd800b80005201ae0129d0032120474028e00edc002480108201ee003dc00eb910800032e010550006001180817f8021c00688019f8009850100000480045003ee8017018210004d
|8,2=>0x240005540022800bf017664069c020ac20db001fe4435d0006010d7000380037c005fc11c7251ee004fc00cb800df28040003dc00db8049f003fe0045000c981464001060015000e78000c063ee00050002a2040d203fe4026c00a6043b70076e00124105780454001ee182bc805980057211ee003dc01a2048c70112e006dc002600104004a8104100241801df003be00010107f900d7000a08014000840004140069001308059840f7401460288101300000000098003dc0886108f3400c800e1c0026015d38008000410025b804110857e003dc886b801af4055e4134c0579801b700098002fc084f820244017e12040808b8480500976007dc0026000df003ee08bfc00cfa00570601c0865c00df8011c
|9,0=>0x885fc04ff821a70037e103dc80df80197202fe007fc12fb800f78013e006dc00db805d3041ee106fc2469905df0232e02ade00ef804df203be003dc14fb810ff041ee0037c10cf821b70032e00afc006f821bf003ee047dc11fb800f74155e127dc807f800df001ee02abc84fb808f70212e0037c08cfa007f0096e0079c007b804b3801be003fc0549801b70036e0224c20fb8049308766812de006f804b7009a6403fd0053a007f2037e103dd005f809d3001fe4067c20dbc31f70016e403fc006f800f74011e00bdc08cf801ff4017f002fe025b820af402fe406fc0a69803ff011a6407fc08fb801ff
|10,0=>0x4b7001fe002fc00ff821ff0116e0037c005b800ff023ee003dc20fb802b7
|11,0=>0xbf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 19 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_187,10,runOps true dom_187 (0,roots_187) ops)] else [])++(if pm.testBit 1 then [(dom_123,10,runOps true dom_123 (0,roots_123) ops)] else [])++(if pm.testBit 2 then [(dom_250,9,runOps true dom_250 (0,roots_250) ops)] else [])++(if pm.testBit 3 then [(dom_243,9,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 4 then [(dom_235,9,runOps true dom_235 (0,roots_235) ops)] else [])++(if pm.testBit 5 then [(dom_219,9,runOps true dom_219 (0,roots_219) ops)] else [])++(if pm.testBit 6 then [(dom_249,8,runOps true dom_249 (0,roots_249) ops)] else [])++(if pm.testBit 7 then [(dom_211,8,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 8 then [(dzo_249_2,7,runOps true dzo_249_2 (0,roots_249) ops)] else [])++(if pm.testBit 9 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 10 then [(dom_242,6,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 11 then [(dom_218,6,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 12 then [(dom_241,6,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 13 then [(dom_233,6,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 14 then [(dom_217,6,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 15 then [(dom_185,6,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 16 then [(dom_248,5,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 17 then [(dom_234,5,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 18 then [(dom_227,5,runOps true dom_227 (0,roots_227) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_251 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_187 _ g hchk
    · exact cpcs (by decide +kernel) low_123 _ g hchk
    · exact cpcs (by decide +kernel) low_250 _ g hchk
    · exact cpcs (by decide +kernel) low_243 _ g hchk
    · exact cpcs (by decide +kernel) low_235 _ g hchk
    · exact cpcs (by decide +kernel) low_219 _ g hchk
    · exact cpcs (by decide +kernel) low_249 _ g hchk
    · exact cpcs (by decide +kernel) low_211 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_249_2_176 _ g hchk
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) low_242 _ g hchk
    · exact cpcs (by decide +kernel) low_218 _ g hchk
    · exact cpcs (by decide +kernel) low_241 _ g hchk
    · exact cpcs (by decide +kernel) low_233 _ g hchk
    · exact cpcs (by decide +kernel) low_217 _ g hchk
    · exact cpcs (by decide +kernel) low_185 _ g hchk
    · exact cpcs (by decide +kernel) low_248 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_227 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_187 10 s (0, roots_187) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_187 h

def symsG : List (List (Nat × Nat)) := []
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_251 == dom_251) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_251 goalM v ys) : RunD true dom_251 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_251 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_36 : ∀ i, 36 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_48 : ∀ i, 48 ≤ i → i < 60 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_60 : ∀ i, 60 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_72 : ∀ i, 72 ≤ i → i < 84 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_84 : ∀ i, 84 ≤ i → i < 95 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 84 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 95 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_324 : ∀ i, 324 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 324 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_336 : ∀ i, 336 ≤ i → i < 348 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 336 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_348 : ∀ i, 348 ≤ i → i < 360 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 348 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_360 : ∀ i, 360 ≤ i → i < 372 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 360 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_372 : ∀ i, 372 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 372 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_384 : ∀ i, 384 ≤ i → i < 396 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_396 : ∀ i, 396 ≤ i → i < 405 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 396 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 405 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72) z7_84) z7_96) z7_108) z7_120) z7_132) z7_144) z7_156) z7_168) z7_180) z7_192) z7_204) z7_216) z7_228) z7_240) z7_252) z7_264) z7_276) z7_288) z7_300) z7_312) z7_324) z7_336) z7_348) z7_360) z7_372) z7_384) z7_396)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_0 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_12 : ∀ i, 12 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_24 : ∀ i, 24 ≤ i → i < 36 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_36 : ∀ i, 36 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_48 : ∀ i, 48 ≤ i → i < 60 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_60 : ∀ i, 60 ≤ i → i < 72 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_72 : ∀ i, 72 ≤ i → i < 84 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_84 : ∀ i, 84 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 84 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_96 : ∀ i, 96 ≤ i → i < 108 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 96 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_108 : ∀ i, 108 ≤ i → i < 120 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 108 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_120 : ∀ i, 120 ≤ i → i < 132 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 120 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_132 : ∀ i, 132 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 132 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_144 : ∀ i, 144 ≤ i → i < 156 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 144 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_156 : ∀ i, 156 ≤ i → i < 168 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 156 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_168 : ∀ i, 168 ≤ i → i < 180 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 168 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_180 : ∀ i, 180 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 180 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_192 : ∀ i, 192 ≤ i → i < 204 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_204 : ∀ i, 204 ≤ i → i < 216 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 204 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_216 : ∀ i, 216 ≤ i → i < 228 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 216 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_228 : ∀ i, 228 ≤ i → i < 240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 228 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_240 : ∀ i, 240 ≤ i → i < 252 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 240 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_252 : ∀ i, 252 ≤ i → i < 264 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 252 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_264 : ∀ i, 264 ≤ i → i < 276 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 264 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_276 : ∀ i, 276 ≤ i → i < 288 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 276 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_288 : ∀ i, 288 ≤ i → i < 300 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 288 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_300 : ∀ i, 300 ≤ i → i < 312 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 300 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_312 : ∀ i, 312 ≤ i → i < 324 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 312 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_324 : ∀ i, 324 ≤ i → i < 336 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 324 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_336 : ∀ i, 336 ≤ i → i < 348 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 336 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_348 : ∀ i, 348 ≤ i → i < 360 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 348 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_360 : ∀ i, 360 ≤ i → i < 372 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 360 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 372 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_12) z8_24) z8_36) z8_48) z8_60) z8_72) z8_84) z8_96) z8_108) z8_120) z8_132) z8_144) z8_156) z8_168) z8_180) z8_192) z8_204) z8_216) z8_228) z8_240) z8_252) z8_264) z8_276) z8_288) z8_300) z8_312) z8_324) z8_336) z8_348) z8_360)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 12 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_12 : ∀ i, 12 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_24 : ∀ i, 24 ≤ i → i < 36 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_36 : ∀ i, 36 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_48 : ∀ i, 48 ≤ i → i < 60 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_60 : ∀ i, 60 ≤ i → i < 72 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_72 : ∀ i, 72 ≤ i → i < 84 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_84 : ∀ i, 84 ≤ i → i < 96 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 84 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_96 : ∀ i, 96 ≤ i → i < 99 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 96 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 99 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z9_0 z9_12) z9_24) z9_36) z9_48) z9_60) z9_72) z9_84) z9_96)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_0 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10_12 : ∀ i, 12 ≤ i → i < 13 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 12 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 13 → Z 10 i = true := (range_split z10_0 z10_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, bar true dom_251 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr true dom_251 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : RunD true dom_251 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_251 roots_251 goal_251 12 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_251

theorem low_251 : Lower true dom_251 roots_251 goal_251 12 := S_251.noCircuit

theorem low_255 : Lower true dom_255 roots_255 goal_255 13 :=
  lower_slice (d:=dom_255) (dSub:=dom_251) (T:=goal_255) (TSub:=goal_251) (roots:=roots_255) (rootsSub:=roots_251)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) low_251

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 13 := low_255

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [4, 8] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [9, 10] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [6, 12] }, { op := GateOp.and, inputs := [0, 13] }, { op := GateOp.or, inputs := [7, 12] }, { op := GateOp.and, inputs := [1, 15] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [3, 17] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [16, 19] }, { op := GateOp.or, inputs := [18, 20] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_30696_aux

theorem PEqualNP.Outside.L_meta_30696 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_30696_aux.main
