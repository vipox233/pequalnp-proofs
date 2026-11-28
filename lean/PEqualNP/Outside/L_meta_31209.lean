import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_31209_aux
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
def goal_255 : Nat := 0xffffffffffffffffffffffffffeeffeefffffffefffffefeffeeffeeeeeeaa00
def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0e0f0e0f0f0f0e0f0f0e0e0f0e0f0e0e0e0a00
def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_250 : Nat := 0x505050505050505050505050504050405050504050504040504050404040000
def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_248 : Nat := 0x101010101010101010101010100010001010100010100000100010000000000
def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_232 : Nat := 0x10100000101000001010000010000000100000000000000010000000000
def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_168 : Nat := 0x1010000010000000000000000000000010000000000
def goal_232_l64 : Nat := 0x10100000101000001010000010000000101000001010000010000000000
def dzo_232_16 : Nat := 0x101000001010000010100000101000001010000010100000101000001010000
def gzo_232_16_64 : Nat := 0x101000001010000010100000100000001010000010100000100000000000000
def dom_240 : Nat := 0x1000100010001000100010001000100010001000100010001000100010001
def roots_240 : List Nat := [xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_240 : Nat := 0x1000100010001000100010000000000010000000100000000000000000000
def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_216 : Nat := 0x1010101000000000100010000000000010100000000000000000000
def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_242 : Nat := 0x5000500050005000500050004000400050004000500040004000400040000
def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_226 : Nat := 0x500000005000000050000000400000004000000040000000400000000
def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_194 : Nat := 0x5000000000000000400000000000000040000000000000000
def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_210 : Nat := 0x50005000000000004000400000000000500040000000000040000
def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_178 : Nat := 0x500050004000400000000000000000004000400040000
def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_162 : Nat := 0x50000000400000000000000000000000400000000
def dom_114 : Nat := 0x50005000500050005000500050005
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_114 : Nat := 0x50004000500040004000400040000
def dom_82 : Nat := 0x500050000000000050005
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_82 : Nat := 0x500040000000000040000
def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_234 : Nat := 0x50500000505000005050000050400000504000004040000050400000000
def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_202 : Nat := 0x505000000000000050400000000000004040000000000000000
def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_170 : Nat := 0x5050000050400000000000000000000050400000000
def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_218 : Nat := 0x5050505000000000504050400000000050504040000000004040000
def goal_210_l128 : Nat := 0x50005000000000005000500000000000500040000000000040000
def dzo_210_8 : Nat := 0x5000500000000000500050000000000050005000000000005000500
def gzo_210_8_128 : Nat := 0x5000500000000000500050000000000050004000000000004000000
def dom_154 : Nat := 0x505050500000000000000000000000005050505
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_154 : Nat := 0x504050400000000000000000000000004040000
def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_186 : Nat := 0x50505050504050400000000000000000504050404040000
def goal_170_l2 : Nat := 0x5050000050400000000000000000000050400000404
def dzo_170_16 : Nat := 0x50500000505000000000000000000000505000005050000
def gzo_170_16_2 : Nat := 0x50500000504000000000000000000000504000004040000
def dom_58 : Nat := 0x505050505050505
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_58 : Nat := 0x504050404040000
def dom_122 : Nat := 0x5050505050505050505050505050505
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_122 : Nat := 0x5050504050504040504050404040000
def goal_114_l32 : Nat := 0x50005000500040005000500040000
def dzo_114_8 : Nat := 0x5000500050005000500050005000500
def gzo_114_8_32 : Nat := 0x5000500050004000500050004000000
def dom_106 : Nat := 0x505000005050000050500000505
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_106 : Nat := 0x504000004040000050400000000
def goal_242_l160 : Nat := 0x5000500050005000500050005000500050005000500040005000500040000
def dzo_242_8 : Nat := 0x500050005000500050005000500050005000500050005000500050005000500
def gzo_242_8_160 : Nat := 0x500050005000500050005000500050005000500050004000500050004000000
def goal_234_l66 : Nat := 0x50500000505000005050000050400000505000005050000050400000404
def dzo_234_16 : Nat := 0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16_66 : Nat := 0x505000005050000050500000504000005050000050500000504000004040000
def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_249 : Nat := 0x303030303030303030303030302030203030302030302020302030202020200
def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_233 : Nat := 0x30300000303000003030000030200000302000002020000030200000200
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
def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_185 : Nat := 0x30303030302030200000000000000000302030202020200
def dom_121 : Nat := 0x3030303030303030303030303030303
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_121 : Nat := 0x3030302030302020302030202020200
def dom_113 : Nat := 0x30003000300030003000300030003
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_113 : Nat := 0x30002000300020002000200020000
def dom_81 : Nat := 0x300030000000000030003
def roots_81 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_81 : Nat := 0x300020000000000020000
def dom_105 : Nat := 0x303000003030000030300000303
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_105 : Nat := 0x302000002020000030200000200
def dom_89 : Nat := 0x30303030000000003030303
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_89 : Nat := 0x30302020000000002020200
def dom_57 : Nat := 0x303030303030303
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_57 : Nat := 0x302030202020200
def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_241 : Nat := 0x3000300030003000300030002000200030002000300020002000200020000
def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_225 : Nat := 0x300000003000000030000000200000002000000020000000200000000
def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_193 : Nat := 0x3000000000000000200000000000000020000000000000000
def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_209 : Nat := 0x30003000000000002000200000000000300020000000000020000
def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_177 : Nat := 0x300030002000200000000000000000002000200020000
def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_217 : Nat := 0x3030303000000000302030200000000030302020000000002020200
def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_201 : Nat := 0x303000000000000030200000000000002020000000000000200
def dom_153 : Nat := 0x303030300000000000000000000000003030303
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_153 : Nat := 0x302030200000000000000000000000002020200
def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_235 : Nat := 0xf0f00000f0f00000f0f00000f0e00000f0e00000e0e00000f0e00000a00
def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_171 : Nat := 0xf0f00000f0e000000000000000000000f0e00000a00
def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_203 : Nat := 0xf0f0000000000000f0e0000000000000e0e0000000000000a00
def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_195 : Nat := 0xf000000000000000e000000000000000e0000000000000000
def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_139 : Nat := 0xf0e00000000000000000000000000000a00
def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_227 : Nat := 0xf0000000f0000000f0000000e0000000e0000000e0000000e00000000
def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_107 : Nat := 0xf0e00000e0e00000f0e00000a00
def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_163 : Nat := 0xf0000000e00000000000000000000000e00000000
def dom_43 : Nat := 0xf0f00000f0f
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_43 : Nat := 0xf0e00000a00
def dom_75 : Nat := 0xf0f0000000000000f0f
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]
def goal_75 : Nat := 0xe0e0000000000000a00
def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_219 : Nat := 0xf0f0f0f000000000f0e0f0e000000000f0f0e0e000000000e0e0a00
def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_91 : Nat := 0xf0f0e0e000000000e0e0a00
def dom_83 : Nat := 0xf000f00000000000f000f
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_83 : Nat := 0xf000e00000000000e0000
def goal_83_l1 : Nat := 0xf000e00000000000e000a
def dzo_83_8 : Nat := 0xf000f00000000000f000f00
def gzo_83_8_1 : Nat := 0xf000e00000000000e000a00
def dom_27 : Nat := 0xf0f0f0f
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]
def goal_27 : Nat := 0xe0e0a00
def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_211 : Nat := 0xf000f00000000000e000e00000000000f000e00000000000e0000
def goal_211_l129 : Nat := 0xf000f00000000000f000f00000000000f000e00000000000e000a
def dzo_211_8 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8_129 : Nat := 0xf000f00000000000f000f00000000000f000e00000000000e000a00
def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_187 : Nat := 0xf0f0f0f0f0e0f0e00000000000000000f0e0f0e0e0e0a00
def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_123 : Nat := 0xf0f0f0e0f0f0e0e0f0e0f0e0e0e0a00
def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_243 : Nat := 0xf000f000f000f000f000f000e000e000f000e000f000e000e000e000e0000
def goal_243_l161 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e000a
def dzo_243_8 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def gzo_243_8_161 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000e000f000f000e000a00
def goal_235_l67 : Nat := 0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0e
def dzo_235_16 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16_67 : Nat := 0xf0f00000f0f00000f0f00000f0e00000f0f00000f0f00000f0e00000e0e0000
def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_179 : Nat := 0xf000f000e000e0000000000000000000e000e000e0000
def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_115 : Nat := 0xf000e000f000e000e000e000e0000
def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_155 : Nat := 0xf0e0f0e0000000000000000000000000e0e0a00
def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_59 : Nat := 0xf0e0f0e0e0e0a00

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

theorem low_232 : Lower true dom_232 roots_232 goal_232 5 :=
  lower_slice (d:=dom_232) (dSub:=dom_168) (T:=goal_232) (TSub:=goal_168) (roots:=roots_232) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x10100000101000000000000000000000101000001010000000000000000, 128, 192)] (by decide +kernel) (by decide +kernel) low_168

theorem low_232_l64 : Lower true dom_232 roots_232 goal_232_l64 5 :=
  lower_slice (d:=dom_232) (dSub:=dom_168) (T:=goal_232_l64) (TSub:=goal_168) (roots:=roots_232) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x10100000101000000000000000000000101000001010000000000000000, 0, 64)] (by decide +kernel) (by decide +kernel) low_168

theorem lowZ_232_16_64 : Lower true dzo_232_16 roots_232 gzo_232_16_64 5 :=
  lower_iso (d1:=dom_232) (roots1:=roots_232) (T1:=goal_232_l64) [(dom_232, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_232_l64

namespace S_240
def pairsG : List (Nat × Nat) := [(16,80), (32,160), (48,112), (48,176), (64,80), (64,192), (96,112), (96,224), (128,160), (128,192), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_240.map (· &&& dom_240)
def goalM : Nat := goal_240 &&& dom_240
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x193b3
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x8000800080008000800080008000800000000000000000000000000000004000400040004000000000000000000040004000400040000000000000002000200000000000200020000000000020002000000000002000200000001000000010000000100000001000000010000000100000001000000010000
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 241 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_240 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_240 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_240 == dom_240) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_240 goalM v ys) : RunD true dom_240 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_240 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_240 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_240 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_240 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_240 roots_240 goal_240 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_240

theorem low_240 : Lower true dom_240 roots_240 goal_240 4 := S_240.noCircuit

namespace S_216
def pairsG : List (Nat × Nat) := [(8,136), (16,80), (24,88), (24,152), (64,80), (64,192), (72,88), (72,200), (128,136), (128,192), (144,152), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_216.map (· &&& dom_216)
def goalM : Nat := goal_216 &&& dom_216
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xd6549
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x8080808000000000808080800000000000000000000000000000004040404000000000000000000000000040404040000000000000002020000000000000202000000000000020200000000000002020001000100000000000100010000000000010001000000000001000100
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 217 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_216 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_216 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffffffffffffffff0000000000000000, 64)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_216 == dom_216) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_216 goalM v ys) : RunD true dom_216 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_216 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_216 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_216 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_216 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_216 roots_216 goal_216 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_216

theorem low_216 : Lower true dom_216 roots_216 goal_216 4 := S_216.noCircuit

namespace S_248
def pairsG : List (Nat × Nat) := [(8,40), (8,136), (16,80), (24,56), (24,88), (24,152), (32,40), (32,160), (48,56), (48,112), (48,176), (64,80), (64,192), (72,88), (72,104), (72,200), (96,104), (96,112), (96,224), (128,136), (128,160), (128,192), (144,152), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_248.map (· &&& dom_248)
def goalM : Nat := goal_248 &&& dom_248
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xb103a0c326
|5,0=>0x711156b50c40faa
|6,0=>0x49137
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x20202020202020202020202020202020202020200000000020202020000000101010101000100010101010100010001010101010001000101010101000100800080008000800080008000800080008000800080008000800080008000800040004000400040004000400040004000000000000000000000000000000020002000200020002000200020002000200020000000000020002000000000101010101010101000000000000000001010101010101010000000000000000808000008080000080800000808000008080000080800000808000008080004040404040404040404040404040404000000000000000000000000000000020202020000000002020202000000000202020200000000020202020000000001000100010001000100010001000100010001000000000001000100000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x241374732192431784132764321543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 249 (i % 32) else 0
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
|0=>0x851749f
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
|5,0=>0x2087
|6,0=>0x1f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 1 then [(dzo_232_16,5,runOps true dzo_232_16 (0,roots_232) ops)] else [])++(if pm.testBit 2 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 3 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])++(if pm.testBit 4 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_248 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_232_16_64 _ g hchk
    · exact cpcs (by decide +kernel) low_240 _ g hchk
    · exact cpcs (by decide +kernel) low_216 _ g hchk
    · exact cpcs (by decide +kernel) low_168 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_232 5 s (0, roots_232) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_248 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_232 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_248 == dom_248) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_248 goalM v ys) : RunD true dom_248 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_248 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_248 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_248 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_248 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_248 roots_248 goal_248 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_248

theorem low_248 : Lower true dom_248 roots_248 goal_248 7 := S_248.noCircuit

namespace S_194
def pairsG : List (Nat × Nat) := [(2,66), (2,130), (64,66), (64,192), (128,130), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_194.map (· &&& dom_194)
def goalM : Nat := goal_194 &&& dom_194
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x82e4b
|3,0=>0x82e4b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140000000000000014000000000000000000000000000000028000000000000000000000000000000280000000000000004000000000000000400000000000000040000000000000004
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 195 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_194 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_194 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_194 == dom_194) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_194 goalM v ys) : RunD true dom_194 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_194 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_194 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_194 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_194 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_194 roots_194 goal_194 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_194

theorem low_194 : Lower true dom_194 roots_194 goal_194 4 := S_194.noCircuit

theorem low_226 : Lower true dom_226 roots_226 goal_226 5 :=
  lower_slice (d:=dom_226) (dSub:=dom_194) (T:=goal_226) (TSub:=goal_194) (roots:=roots_226) (rootsSub:=roots_194)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500000000000000050000000000000005000000000000000500000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_194

theorem low_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_slice (d:=dom_210) (dSub:=dom_194) (T:=goal_210) (TSub:=goal_194) (roots:=roots_210) (rootsSub:=roots_194)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50000000000000005000000000000000500000000000000050000, 2, 18)] (by decide +kernel) (by decide +kernel) low_194

namespace S_162
def pairsG : List (Nat × Nat) := [(2,34), (2,130), (32,34), (32,160), (128,130), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_162.map (· &&& dom_162)
def goalM : Nat := goal_162 &&& dom_162
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x99177
|3,0=>0x99177
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140000001400000000000000000000000000000002800000000000000000000000000000028000000040000000400000000000000000000000400000004
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 163 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_162 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_162 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_162 == dom_162) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_162 goalM v ys) : RunD true dom_162 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_162 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_162 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_162 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_162 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_162 roots_162 goal_162 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_162

theorem low_162 : Lower true dom_162 roots_162 goal_162 4 := S_162.noCircuit

theorem low_178 : Lower true dom_178 roots_178 goal_178 5 :=
  lower_slice (d:=dom_178) (dSub:=dom_162) (T:=goal_178) (TSub:=goal_162) (roots:=roots_178) (rootsSub:=roots_162)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500000005000000000000000000000005000000050000, 2, 18)] (by decide +kernel) (by decide +kernel) low_162

namespace S_82
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (16,18), (16,80), (64,66), (64,80)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_82.map (· &&& dom_82)
def goalM : Nat := goal_82 &&& dom_82
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xe8a40
|3,0=>0xe8a40
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140014000000000000000280000000000000028000400040000000000040004
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 83 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_82 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_82 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
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

theorem low_82 : Lower true dom_82 roots_82 goal_82 4 := S_82.noCircuit

theorem low_114 : Lower true dom_114 roots_114 goal_114 5 :=
  lower_slice (d:=dom_114) (dSub:=dom_82) (T:=goal_114) (TSub:=goal_82) (roots:=roots_114) (rootsSub:=roots_82)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000000000005000500000000, 2, 34)] (by decide +kernel) (by decide +kernel) low_82

namespace S_242
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,66), (2,130), (16,18), (16,80), (32,34), (32,160), (48,50), (48,112), (48,176), (64,66), (64,80), (64,192), (96,98), (96,112), (96,224), (128,130), (128,160), (128,192), (144,146), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_242.map (· &&& dom_242)
def goalM : Nat := goal_242 &&& dom_242
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xd0973
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x5000500050005000500050005000500000000000000000000000000000000a000a000a000a0000000000000000000a000a000a000a000000000000000140014000000000014001400000000001400140000000000140014000000028000000280000002800000028000000280000002800000028000000280004000400040004000400040004000400040004000400040004000400040004
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 243 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 1 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 2 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 3 then [(dom_114,5,runOps true dom_114 (0,roots_114) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_242 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_226 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_114 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_226 5 s (0, roots_226) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_242 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_226 h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_242 == dom_242) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_242 goalM v ys) : RunD true dom_242 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_242 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_242 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_242 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_242 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_242 roots_242 goal_242 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_242

theorem low_242 : Lower true dom_242 roots_242 goal_242 7 := S_242.noCircuit

theorem low_202 : Lower true dom_202 roots_202 goal_202 5 :=
  lower_slice (d:=dom_202) (dSub:=dom_194) (T:=goal_202) (TSub:=goal_194) (roots:=roots_202) (rootsSub:=roots_194)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500000000000000050000000000000005000000000000000500, 128, 136)] (by decide +kernel) (by decide +kernel) low_194

theorem low_170 : Lower true dom_170 roots_170 goal_170 5 :=
  lower_slice (d:=dom_170) (dSub:=dom_168) (T:=goal_170) (TSub:=goal_168) (roots:=roots_170) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4040000040400000000000000000000040400000404, 32, 34)] (by decide +kernel) (by decide +kernel) low_168

namespace S_234
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (2,130), (8,40), (8,136), (10,42), (10,74), (10,138), (32,34), (32,40), (32,160), (64,66), (64,192), (72,74), (72,104), (72,200), (96,98), (96,104), (96,224), (128,130), (128,136), (128,160), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_234.map (· &&& dom_234)
def goalM : Nat := goal_234 &&& dom_234
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xa5321
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x50500000505000005050000050500000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a0a000000000000000141400000000000014140000000000001414000000000000141400000002800000028000000280000002800000028000000280000002800000028040400000404000004040000040400000404000004040000040400000404
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 235 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 1 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 2 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 3 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_234 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) low_226 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_232 5 s (0, roots_232) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_234 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_232 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_234 == dom_234) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_234 goalM v ys) : RunD true dom_234 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_234 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_234 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_234 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_234 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_234 roots_234 goal_234 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_234

theorem low_234 : Lower true dom_234 roots_234 goal_234 7 := S_234.noCircuit

theorem low_210_l128 : Lower true dom_210 roots_210 goal_210_l128 5 :=
  lower_slice (d:=dom_210) (dSub:=dom_82) (T:=goal_210_l128) (TSub:=goal_82) (roots:=roots_210) (rootsSub:=roots_82)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000000000005000500000000000000000000000000000000, 0, 128)] (by decide +kernel) (by decide +kernel) low_82

theorem lowZ_210_8_128 : Lower true dzo_210_8 roots_210 gzo_210_8_128 5 :=
  lower_iso (d1:=dom_210) (roots1:=roots_210) (T1:=goal_210_l128) [(dom_210, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_210_l128

namespace S_154
def pairsG : List (Nat × Nat) := [(2,18), (2,130), (8,136), (10,26), (10,138), (16,18), (24,26), (24,152), (128,130), (128,136), (144,146), (144,152)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_154.map (· &&& dom_154)
def goalM : Nat := goal_154 &&& dom_154
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xf52fe
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a0a0a0000000000000000000000000000000141400000000000000000000000000001414000280028000000000000000000000000002800280404040400000000000000000000000004040404
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 155 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_154 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_154 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_154 == dom_154) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_154 goalM v ys) : RunD true dom_154 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_154 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_154 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_154 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_154 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_154 roots_154 goal_154 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_154

theorem low_154 : Lower true dom_154 roots_154 goal_154 4 := S_154.noCircuit

namespace S_218
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (2,130), (8,136), (10,26), (10,74), (10,138), (16,18), (16,80), (24,26), (24,88), (24,152), (64,66), (64,80), (64,192), (72,74), (72,88), (72,200), (128,130), (128,136), (128,192), (144,146), (144,152), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_218.map (· &&& dom_218)
def goalM : Nat := goal_218 &&& dom_218
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x841b3
|5,0=>0x1b892
|6,0=>0x33489
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x141400000000000014140000000000001414000000000000141400028282828000000002020202000000000282828280000000020202025050505000000000505050500000000000000000000000000000000a000a00000000000a000a00000000000a000a00000000000a000a0141414140000000000000000000000001414141400000000000000020202020000000002020202000000000202020200000000020202020000505000000000000040400000000000005050000000000000404
|_,_=>0
def stPool : Nat → Nat
|0=>0x8b333346c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 219 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 1 then [(dzo_210_8,5,runOps true dzo_210_8 (0,roots_210) ops)] else [])++(if pm.testBit 2 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 3 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])++(if pm.testBit 4 then [(dom_154,4,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 5 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_218 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_210_8_128 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_216 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_82 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_210 5 s (0, roots_210) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_218 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_210 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_218 == dom_218) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_218 goalM v ys) : RunD true dom_218 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_218 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_218 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_218 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_218 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_218 roots_218 goal_218 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_218

theorem low_218 : Lower true dom_218 roots_218 goal_218 7 := S_218.noCircuit

theorem low_170_l2 : Lower true dom_170 roots_170 goal_170_l2 5 :=
  lower_slice (d:=dom_170) (dSub:=dom_168) (T:=goal_170_l2) (TSub:=goal_168) (roots:=roots_170) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4040000040400000000000000000000040400000404, 0, 2)] (by decide +kernel) (by decide +kernel) low_168

theorem lowZ_170_16_2 : Lower true dzo_170_16 roots_170 gzo_170_16_2 5 :=
  lower_iso (d1:=dom_170) (roots1:=roots_170) (T1:=goal_170_l2) [(dom_170, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_170_l2

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

namespace S_186
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,130), (8,40), (8,136), (10,26), (10,42), (10,138), (16,18), (24,26), (24,56), (24,152), (32,34), (32,40), (32,160), (48,50), (48,56), (48,176), (128,130), (128,136), (128,160), (144,146), (144,152), (144,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_186.map (· &&& dom_186)
def goalM : Nat := goal_186 &&& dom_186
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x72f95
|5,0=>0x22d75
|6,0=>0x54d66
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x1400140014001400000000000000000014001400140014028282828282828280000000000000000282828280000000505000005050000000000000000000005050000050500008080808080808080000000000000000080808080808080941414141414141400000000000000000000000000000002828282800000000000000000000000028282828000000000500050005000500000000000000000005000500000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x46673346c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 187 (i % 32) else 0
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
|5,0=>0x17
|6,0=>0x3d
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 1 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 2 then [(dzo_170_16,5,runOps true dzo_170_16 (0,roots_170) ops)] else [])++(if pm.testBit 3 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 4 then [(dom_154,4,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 5 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_186 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_170_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_168 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_58 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_178 5 s (0, roots_178) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_186 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_178 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_186 == dom_186) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_186 goalM v ys) : RunD true dom_186 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_186 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_186 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_186 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_186 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_186 roots_186 goal_186 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_186

theorem low_186 : Lower true dom_186 roots_186 goal_186 7 := S_186.noCircuit

theorem low_114_l32 : Lower true dom_114 roots_114 goal_114_l32 5 :=
  lower_slice (d:=dom_114) (dSub:=dom_82) (T:=goal_114_l32) (TSub:=goal_82) (roots:=roots_114) (rootsSub:=roots_82)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000000000005000500000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_82

theorem lowZ_114_8_32 : Lower true dzo_114_8 roots_114 gzo_114_8_32 5 :=
  lower_iso (d1:=dom_114) (roots1:=roots_114) (T1:=goal_114_l32) [(dom_114, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_114_l32

namespace S_106
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (8,40), (10,42), (10,74), (32,34), (32,40), (64,66), (72,74), (72,104), (96,98), (96,104)]
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

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)]]
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

namespace S_122
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,66), (8,40), (10,26), (10,42), (10,74), (16,18), (16,80), (24,26), (24,56), (24,88), (32,34), (32,40), (48,50), (48,56), (48,112), (64,66), (64,80), (72,74), (72,88), (72,104), (96,98), (96,104), (96,112)]
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
|4,0=>0xb64443fe28
|5,0=>0xd3c79629692a1e1
|6,0=>0xefe43
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x28282828282828282020202020202020000000000000000404040404040404a0a0a0a0a0a0a0a000000000000000141414141414141414140000141400028282020282820200000000000000005050505000000000505050500000000a000a000a000a000a000a000a000a0141400001414000014140000141400020202020202020202020202020202020000000000000000505040405050404
|_,_=>0
def stPool : Nat → Nat
|0=>0x742312437192437184317264321543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 123 (i % 32) else 0
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
|0=>0x1c5719c9
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
|5,0=>0x4264
|6,0=>0x1f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_114,5,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 1 then [(dzo_114_8,5,runOps true dzo_114_8 (0,roots_114) ops)] else [])++(if pm.testBit 2 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 3 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])++(if pm.testBit 4 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_122 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_114_8_32 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_82 _ g hchk
    · exact cpcs (by decide +kernel) low_58 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_114 5 s (0, roots_114) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_122 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_114 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)]]
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

theorem low_242_l160 : Lower true dom_242 roots_242 goal_242_l160 6 :=
  lower_slice (d:=dom_242) (dSub:=dom_210) (T:=goal_242_l160) (TSub:=goal_210_l128) (roots:=roots_242) (rootsSub:=roots_210)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5000500000000000500050000000000050005000000000005000500000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_210_l128

theorem lowZ_242_8_160 : Lower true dzo_242_8 roots_242 gzo_242_8_160 6 :=
  lower_iso (d1:=dom_242) (roots1:=roots_242) (T1:=goal_242_l160) [(dom_242, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_242_l160

theorem low_234_l66 : Lower true dom_234 roots_234 goal_234_l66 6 :=
  lower_slice (d:=dom_234) (dSub:=dom_232) (T:=goal_234_l66) (TSub:=goal_232_l64) (roots:=roots_234) (rootsSub:=roots_232)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x40400000404000004040000040400000404000004040000040400000404, 0, 2)] (by decide +kernel) (by decide +kernel) low_232_l64

theorem lowZ_234_16_66 : Lower true dzo_234_16 roots_234 gzo_234_16_66 6 :=
  lower_iso (d1:=dom_234) (roots1:=roots_234) (T1:=goal_234_l66) [(dom_234, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_234_l66

namespace S_250
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,66), (2,130), (8,40), (8,136), (10,26), (10,42), (10,74), (10,138), (16,18), (16,80), (24,26), (24,56), (24,88), (24,152), (32,34), (32,40), (32,160), (48,50), (48,56), (48,112), (48,176), (64,66), (64,80), (64,192), (72,74), (72,88), (72,104), (72,200), (96,98), (96,104), (96,112), (96,224), (128,130), (128,136), (128,160), (128,192), (144,146), (144,152), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_250.map (· &&& dom_250)
def goalM : Nat := goal_250 &&& dom_250
def NN : Nat → Nat
|2=>0x2
|3=>0x5
|4=>0x13
|5=>0x59
|6=>0xa7
|7=>0x4c
|8=>0xc
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xb88cd1eb14
|3,0=>0xfc1d2db19266c5b60c7b413d9
|4,0=>0xf6106d969ad2ad8d0da2cb011993ed8a93289520835408249b7076838361307e624cd31ea971797510a070b37201384
|5,0=>0xed246e38d1e34e9dd263cfcf7c823ac6ae5c2ebcc0343be9f8bdbcdbc822b92d8b6d38af71eaf2f0ac037a55eaa4d60a3c0ba2852a17039ea9c9d7789759b968ad9336f9302d8e19986d6a85b36852287f68473b997257f6ee766c2a86abed6267161a275f4525e5905ac2658a7e57fcc5616255dbb545a4522c751a10442d643de040f8d3eca93db983ce613c6e73b6da3ae7e3a23a36d95288b12777e212ac1fc8d1dc271d0541af131abec1a3d6196131833b172e01481713de0132c0119dd1187610e5610acb0de370c5cd0a85d0a6100894105afc02c27021f7007b1
|6,0=>0x921f890b608e32c8d88a8cd6f89548880218787984f3c84f3683c5c83bdf819bb7f08a7c7777b4f27a8b47585d7561b72eb17259370a7a6fb176c8c26c17e6b8ed6aaa16a547664a4645f26400162e0962bf8626e4626d55d16d5ca985c19b5b87b5965a57a47573af54b965462e530d5512e950cfb4ec2f4eb614e1fa4c2b34bf844a11748e634813c476ca472ed47172417213f9c13f3d93d9303ccde3cb053bae43b8953b75a3ac003a14539f6738e943743136a7d361003402a33983330d331dde31d313037e300572fea42f3932e4482d0432be712a15329b35296e2287182717c250c524f9d225d120fa01f5001eeb71dea01dab41c6b01ab901aa1a1a80d19947197631721616d7015bfc14c0b14bfd14a8f13b4010d8410c780fb0b0f6e50f0f00c91e0c86b0c29a0bc6409044041600361c02c2a01e070089500522
|6,1=>0xe699edad95d84bdd63f0d55fdd52bbd3ce6d1b63c9a41c5808c579ac2d18c121dc0eabbfec5bf0dabdbe1b9172b8babb6299b5b95b5247b4722b44a8b2d72b2895af3a2a5543a5227a3035a10d09fcee9d6329ce7c974589727396a9d960c8924ca
|7,0=>0xf7ec2e65ded422ad100dc9cdec44dfc142abd64bbcbe9b9b38ab68b9f71d939c78ea438a631889c98570f815c27e080776ca76977760da72c2a70951708806c7056952262563603215fa115e4a35532852d724c1ad4962b4947c485f342f233fc993defa3dbca38b793899b374c236f06368ce33f85323b732041317cd31131311292f4352da022d1962ce7c2b3291d38c1ad311a11f17f8d1642b15c4a1498610f561060d1022d0efa80eba50e21d094ec08c6d07fa6027ae02251021de
|8,0=>0xf38e2bfeefb8f7b9ff7169d9c483793c660353022cb2b27b021eb5209cda
|9,0=>0xf38e2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa080a080a080a080a080a080a080a080a080a080a0800000a080a080a08000141414141414141414141414140014001410141014101410141014101400140282828282828282820202020202020202828282828282828202020202020202505050505050505050505050000000004040404040404040404040400000000a0a0a0a0a0a0a0a0a080a080a080a080a0a0a0a0a0a0a0a0a080a080808080941414141414141414101410141014101414000014140000141000001410000282800002828000020200000202000002828000028280000202000002020000505050505050505050505050505050505050505000000000505050500000000a0a0a0a080808080a0a0a0a080808080a0a0a0a080808080a0a0a0a0808080941014101410141014101410141014101410141014101410141014101410141000028280000282800000000000000000000282800002828000028200000282504050405040504050405040504050405040504050405040504050400000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a000141414141010101014141414101010101414141410101010000000000000000282828282828282828282828282828282020202020202020202020202020202000050500000505000005040000050400000505000005050000050400000404a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a00000a0a000001400140000000000140014001400140014001400000000001400140014000280028002800280028002800280028002800280028002800280028002800280505050505050505050505050505050505050505050505050000000000000000a0a0a0a0a0a0a0a0a0a0a0a080808080a0a00000a0a00000a0a00000808000141414001414140014101400141014001414140014140000141014001010000202020202020202020202020202020202020202020202020202020202020202500050005000500050005000500050005000500000000000500050000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000000000000000000000000000141400001414000014100000141000001414000014140000141000001010000282828280000000028282828000000002828282800000000282828280000000505050505050505000000000000000005050505050505050000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0000080800000808000141414141414141414141414000000001414141414141414141414140000000282028202820282028202820282028202820282020202020282028202020202505050505050505050505050505050505050000050500000504000004040000
|0,1=>0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0800000a0941414141414141414101410141014101414141414141414141014101410141000000000000000000000000000000002828282828282828282828282820282505050505050505050505050505050505050505040404040505050504040404000000000000000000000000000000000000000000000000a080a080a080a080000000000000000404040404040404000000000000000004040000040400000000000000000000000000000000000000000002820282000000000282028250405040504050405040504050405040504000005040000050400000504000000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a080a0800000001414141400000000141414140000000010101010000000001010101000000002800280000000000282828280000000028002800000000002820282505050505050505050505050505050505050500050505000504050005040500a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a080a080a080a080a080a0800000001414141400000000141414140000000014101410000000001410141282828282828282828282828282828280000282800002828000028280000202505050500000000050505050505050505050505000000000505050505050000a020a020a020a020a020a020a020a020a020a000a020a000a020a000a020a014141414141414141414141414141414141414141414141414141414000000028282828282828282828282828282828282828282828000028282828202000000005050000050500000000000005040000050500000505000000000000050400000000a080a08000000000a080a08000000000a080a08000000000a080a094141414141414141414141414140000141410101414101014141010141400000000000282828280000000028282828000000002828000000000000282800000000000000000005050505050505050000000000000000040404040404040400a000a000a000a000a000a000a000a000a000a000a000a000a000a000a00014141414141414140404040404040404141414141414141404040000040400000002020000020200000202000002020000028280000282800002828000020200500050005000500050005000500050005000000050000000400000004000000a000a000a000a000a000a000a000a000a000a000a000a000a000a0000000000000000000000014141414141414140000000000000000141400001414000080008000800080008000800080008000800080008000800080008000800080005000500050005000500050005000500050005000000000005000500000000
|0,2=>0xa0a0a0a0a0a08080a0a0a0a0a0a08080a0a0a0a0a0a08080a0a0a0a0a0a080800000000000000000000000000000001414141414141010141414141414101080808080808080808080808080808080808000008080000080800000808000505050505050000050505050505000005050505050500000505050505050000a0a0a0a0a0a0a0a0a000a000a000a000a0a0a0a0a0a0a0a0a000a000a000a0141414141414141400140014001400141414141414141414001400000014000280828082808280828082808280028002808280828082808280828082800280500050005000500050505050505050505000500050005000505050005050500a0a0a0a0a0a0a0a0a0a0a0a080808080a0a0a0a0a0a0a0a0a0a0a0a0808080800000000000000014141414101010100000000000000000141414141010101000800080008000800080008000800080008000800080008000800080000000005000500050005000500050005000500050005000500050005000500040004a0a0a0a020202020a0a0a0a020202020a0a0a0a020200000a0a0a0a02020001010101010101010141414141414141410101010101010101414101014141012828282828282828282828282828282828002800280028002800280028002800000505000005050000000000000505000005050000050500000000000004040000000000000000a080a080a080a0800000000000000000a080a08080808080000000141414140000000014141414000000001414141400000000000000028282828282828282828282828282828000028280000282800002820000028200005050000050500000404000004040000050500000505000004040000040400a000a00020002000a000a00020002000a000a00020002000a000a0000000001400140014001400140014001400140014001400100010001400140010001282828282828282828282828282828282828282828280000282828282828000005000500010001000500050001000100050005000100000005000500010000a0a0a0a080808080a0a0a0a080808080a0a0000080800000a0a00000808000000400040004000400040004000400040004000400040000000400040004000000000000000000028202820282028200000000000000000282028202820282000000000000000000000000504050400000000000000000000000005040504a0a0a0a0a0a0a0a0a0a00000a0a00000a0a0a0a0a0a0a0a0a0a00000a0a000141014101410141014101410000000001410141014101410141014100000000080808080808080808080808080808080808080808080808000000000000000101010101010101010101010000000001010101010101010101010100000000
|0,3=>0xa0a0a0a0a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a000001400140014001400140014001400140014001400140000001400140014000282828282828282828282828282828282828202028282020282820202828202505050501010101050505050101010105050505010101010505050500000000000000000000000000000000a0a0a0a0000000000000000000000000808080941414141414141414141414141414140000000014101410000000001410141000000000000000028282828282828280000000000000000282828282020202405040504050405040504050405040504050404040504040405040404050404a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a0a0a0a0a0a0a0a0a0a0a0a0000000000000000000000000000000000014141414141414141414141414140000000000000000000000000000000000028280000282800002828000028280005010501050105010501050105010501050105010501050105000500050005000000a0a00000a0a00000a0a0000080800000a0a00000a0a00000a0a000008080140014001400140014001400140014001400000014000000140000001400000000000000028280000000000002828000000000000202000000000000020200000000000000000000000000000000505050505050505050505050000000080808080a0a0a0a080808080a0a0a0a080808080a0a0a0a080808080808080800000000404040400000000040404040000000004040000000000000404000282828282828282828282828282828282828282828282828202020202020202000050500000505000005050000000000000505000005050000050500000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a00000a0a00000a0a00000000014001400140014001400140014001400140014001400140000000000000002028202820282028202820282028202820282028202820282020202020202025000505050005040500050505000504050005050500050405000505050005040000a0a00000a0a00000a0a00000a0000000a0a00000a0a00000a0a00000a0001400140014001400140014001000100014001400140014001400140010001000000000000000028282828282028200000000000000000282828282820282005000500050005000500050005000500050004000500040005000400050004a0a0a0a000000000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0a0a0808080941414141414141414141414141414140000000000000000141014101410141000000000000000000000000000000002828282828282828282828282020202505050500000505050505050000050505050505000004040505050500000404
|0,4=>0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080a080a080a090141014101410141014101410141014101410141010101010141014101010100280028002800280028002800280028002000200020002000200020002000200500050005000500050005000500050005000500050005000400040004000400a000a000a000a000a000a000a000a000a000a000a000a000a0000000a0001414141414141414000000001410141014141414141414140000000014101412828282800000000282828282820282028282828000000002828282828202820000000000000000000000000000000050505050404040405050505040404040000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a000000000000000000000000000000000000000000000000000141414141010101282800282828002828280028282800002828002828280028282800282828000500050005000500050505050505050505000500050005000504050405040504000000000000000000000000a0a0a0a0000000000000000000000000a0a000141414141414141414141414141414141414141414141414140014001400140002800280028002000280028002800200028002800280020002800280028002505050505050505050505050505050505050505050505050505050504040404a0a000a0a0a000a0a0a000a0a0a000a0a0a00080a0a00080a0a00080a0a000941414141414141414141414000000001414000014140000141400000000000282800002828000028280000282800002828282028282820282828202828282504050405040504050405040504050405040504050405040000000000000000a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080000000000000000000000000000000141014101410141014101410141014128282828282828280000000000000000282828282828282828202820282028200005050000050500000505000005050000050500000505000004040000040400000000000000000000000000000000202020202020202020202020000000141414141414141414141414141414141414141414141414141414141414000282800002828282028280000282828202828000028282820282800002828282101010101010101010101010101010101010101010100000101010101010000a0a0a0a00000a0a0a0a0a0a00000a0a0a0a0a0a00000a0a0a0a0a0a0000000141400141414001014140014141400101414001414140010141400141414001000000000000000028282828282828280000000000000000282028202820282505000005050505050500000505050505050000050505050505000005050000
|0,5=>0xa0a00000a0a00000a0a00000a0a0000080800000808000008080000080941414141400140014141414140014001414141414001400141414141400140282828282820282028282828282028202828282828202820282828282820282505050505050505050505050505050505050505050505050505000005050000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a000a0a0a0001400140010001000140014001000100014001400100010001400140010001000028200000282000002820000028200000282000002820000028200000282404040404040404040404040404040405050505050505050505050504040404
|_,_=>0
def stPool : Nat → Nat
|0=>0x23050f220c0921130d170c1c0409030520041105131f131804091e130d1d181c130702011b050c090d1a0409030508050701040609020708190d180209030f0c02171605160411151311050414050709040a130d0212110507010410090f050c0e0d0c05090b0902070a04030501020903080702010605010400020301020100
|1=>0x9030d34131611180402130d1d05071c040f09110d320d0509040731130d17020c11090d0f05300c0d0905020305040f0d2f110d13052e111d0d040903052d07090516042c04162b17070f0d090705042a04050f291116050d0f22092809040705132716110f040502050d0f0426110d0405070925050409030d24090f040c05
|2=>0x413161707360d0f0c05094013161704072e05040f22111604090705131f050407090d3f050f11040d3e13161105042e0405110f1638130509040d3d041316073c3605131104163b050d0c090f3a041311051639130d051104120d0f0c0209170504110d0f38130407090d37040d0f113617130907040d3516170402070f0504
|3=>0x111d0504090d074d130d0902071205070809044c0d040903051804160f11053613040709054b040f0911054a13161105020c041617071349041307090548040d13110547071317041642040907051346050f110d044513091d0207080d130c05091c0713170416440507041343011605170f040c07130d1704420d0f05020941
|4=>0x4c050720050413110d38130d05570c110d0f110504561309040507551305090407540d090502070305130c110d3e040d11050f47040d0f05531113160402073c04160f11053c050907160415050d0f09520c050d5104090309130704050e0507080904191309040507140d070905045013050701044f0413161136180d13054e
|5=>0x4056305130d0904076207130d16170402130d041d110518130d0509040761040d090713056009050704134308040d050f29091105130d1d071128040d050913075e0d0f09110504021309160502070c05040d0f5d11040d17135c07110905130f0c0d5b0905070d0f045a13070504090d59130d1d02181109050f0d580c0409
|6=>0x13040705096f050d0709040f3a040d0709050f6e0d13070502096d090d050413076b051304070d09690d1307054e091d07040509130d68070904050d136707130509040d660d131804020911071305090d04650413160711053c05040907130d64090d0f040c052e071309162b04020907135c020d5b05040f110d160d130907
|7=>0x160711046d0405160711137d0d13040709057c130d070905047b0413090516077a130d0509070479070d09050219050413070d0978090d050413077604160517077505130407090d740d070504090273050d0f04094105040d0f720911050d130c111d130d050456071105130904160762040d0709051371130916040507700d
|8=>0x7090d2f130d070904051c0d070f09050456040916071305290d1304052e0911070405090d13820513070c090d3e051307090d0481040d0709050f47090d040705138004130d09073c36040d07090f0553130d051711040c04160517070f05131607110428041307090d32041316110518090d07050f047f09040507137e0513
|9=>0x2004050d090713380d070f0502091d0d0f040c050917040d130f11051705131611040c04130d09170736050d04070c0988050d130c091128130d0709040587050d040f220911130d050957070c090d040705138607040d0905138509130407052e230d130718040940040d0507130984090d0407130583050d0f0c091d050413
|10=>0x40c0d9207040509130d9104050907131638040905162b07750416071105135c130d0509040790130d091d020718040507090d138f040d0513490911090d130705048e0405090716138d0704090516138509050f0c0d5b05130d0907048c0413098b05070805130d09070489091304070c0523050d0f040c096d090507041343
|11=>0x7030d1307052e091d050d0f04096d090d0507130497090d0f0c05020407050f2909160916070f040502050d04070988050d07090f042604130509073c4a1305070809041d0d130c050209110d130407050996070904050d139505130907040d94040905162b070f0504070d0f097804130709110d32090d130705049309050f
|12=>0x90d0705040f8e090513070d045a09050d0f72040c050f040c0d09160413098b0507200504130f110d1607130d0905049a07130905020d3e05130d0907043b050d090f5d040c07130d09040599130d0904020798090d13072205020d04094c050718090d050f29040c130d091702070c050d0f090428091304070523050d0409
|13=>0xd04050709a0050d0f09110428040516110f071309170d5b0205130407090d9f04130507099e05040f09110d9d050d0907110488070413162b170713090516049a05070f09040d3e040d1305290911090d0705040f931309160405072e05130407090d9c040509070f16380d13040705091209050407130d9b0d13070c050940
|14=>0x130d05170711090d0705041377090d05071804134304130d070911053c05130d091607040c090d13070f050402090d07135c040207130d091d050205130d041d0711130d09040507700405130907168a09051304070d92090504070c130da3050413070f092107041305090da2070405091316a107050d040919050d04090313
|15=>0x517050d130907110428090705135c040d5b05040d1307095d040513160711090d130407054e05040d090711137d0405130709110d9d04050d091607130f09050d04070c13a40704130905162b09050d0751041343050d070f09041d0704130d160517040d077509051709040d1307052909051304070d6a0704130d09052b04
|16=>0xd330709130da3040502040d13098b050718130d0709110405020907041343050da607041305090da509050d0f040c04050921077504050916070f07130921040502090d07050402137704050916077504130d0917071809050413070d720704091605135c0513070911040d5b0713091604050209050775040d5b040d070f09
|17=>0x17135f050d1304070c096d0d130705040902570d1304070c05091704130d0709053605040d090713a70504070f090d160d1305071804091d050d130407094107130d0509045705040d075113098b07040d091605135c0405070911130da307051304090d3e09040d07050f29090d1304070c052e05040d130f09110405130709
|18=>0x70405130d0909050d1304070c090504130d075109040d1305071809050d07041343070405130d091607040509130da30405130d07091109040d0705135c07130d090405020704051309210704051309160713050917040d5b09041305072004130d0509073c07130d09170402090d070504136c090513070c0d5b07040d0509
|19=>0x70405130d09
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x330003
|3,0=>0x164012400e400a40064
|4,0=>0x74506f506a50655060505b50565051504c50475042503d50385033502e50295024501f501a5
|5,0=>0x1f261ec61e661e061da61d461ce61c861c261bc61b661b061aa61a4619e61986192618c61866180617a6174616e61686162615c61566150614a6144613e61386132612c61266120611a6114610e6108610260fc60f660f060ea60e460de60d860d350cd60c760c160bb60b560af60a960a3609d60976091608b6085607f60796
|5,1=>0x2886282627c62766270626a6264625e62586252624c62466240623a6234622e62286222621c62166210620a620461fe61f86
|6,0=>0x43d7436742f74287422641b7415640f6408740263fb73f473ed73e673df73d873d263cb73c473be63b773b073aa63a3739d6396738f73887381737a7373736c7365735e7357735073497342733b7334732d7326731f73187311730a730462fd72f672ef72e872e172da72d372cc72c572be72b772b072aa62a3729c7295728e7
|6,1=>0x5f775f165ea75e465dd75d675d065c975c275bb75b475ad75a6759f75987591758a7583757c7575756e7567756075597552754b7544753d7536752f75296522751b7514750d750674ff74f874f174ea74e374dd64d674cf74c874c174ba74b374ac74a5749e7497749074897483647c7475746e7467746074597452744b74447
|6,2=>0x70156fa76f376ee56e776e076da66d376cc76c666bf76b876b176aa76a3769c7695768e7687768076797672766b7664765d7656764f76487641763a7633762c7625761e76177610760a660465fe6
|7,0=>0x8d078c888c178ba78b288aa88a2889b7894788c8885787e7876886e8866885e88577851684b6845683e7836883068297822781b7813880c780577fe77f687ee87e777e167da77d287ca87c287ba87b377ab87a4779d7796778f77887781777a7773776b8763875b8753874c7745773e7737773077297721871a7713770c77066
|7,1=>0x9278921691a7913790c790578fd88f588ed88e588de78d77
|8,0=>0x97a6973796c7965795e7957795079497942793b7935692f6
|9,0=>0x9806
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 168 then fld (dictB (i / 512) (i / 32 % 16)) 251 (i % 32) else 0
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
|0=>0xf1601c4d0709434253c05c5c1d0509434250f1dc1025040744c1d181681c150709434250c1701c110907414250f1602435090744c1d030d41c651d1301025040541c15070943425110201c250504410253305c4435090744c1d07194744c05044102504094241d0c054101d030541c651d13010250d0941c25050f84c1d040541c4d070943425030dc1c651d1301025
|1=>0x1d0d4241107094101d170f02415090744c1d170741411050943425110541c4d0709434250104c2421180d0141d0507444170709434251105c1c4d0709434253c0dc4415090744c1d0f1701425090744c1d160201411050943425041682435090744c1d11020241d04054101d08094603404134141d0216010150509434253c05c5c1d0509434250d094241d040f84c1d
|2=>0x4054145a0d094103504054144d090d4241d1307414a11104c241d0405414250d0941c15090741025075785c1105094603404134141d07094143e1307444130907410255f07c5c4d050941411090744c1d0704410150d094241d090f84c1d09074144d050941035040744c1d070941c150504410250f1603425090744c1d070941c1117044142507194744c050441025
|3=>0xd09410a5050f84c1d490dc604d050744411070943425111341c250d09415050c09c101d072b4145a0d094744c05044102509724343e130741dde0213414111307c14250d0955c4f0902414110c09c101d13074241d0d0f84c1d090441c2504074241d1704c14250f1dc241113074243104054101d076c4084f0504425a90c0dc101d110541c250d0943015040744c1d
|4=>0x1707414256d13c302504074441307094101d09074103e130741c111704414252e134301504074b8370c054101d09028101505074252618134141d04094101d130744408040541c25050f81c4d0d094241d0c054101d1d0d41025040743c5c090544c1d134e4301704074f017170741425055d4243e130744c1d0509434251104c1c250d094cc17110d41c25070541c25
|5=>0x160f01c4d0d0941c4e051683425051341c250d0941d5d17044142507054141104094241d18134141d0f0201411130744e29071683425132b4145a0d0941035040744c1d0c1601c110d0946034050744c25048a41c5a0d094b8370c054101d0c094101d13074603704134141d0f1601c4d0d0942411050444c1d05094101d130741425090744c1d070441c250d094f017
|6=>0x13074141d1d13c102507044143e130744413090744c1d2e0dc3015040741c651d1301025090443015040743025040744c1d4904c604d050741015040744c1d0d094143e1307410150713434256d13c3025040741175090f84c1d3c0dc5c1d050942411180d0141d0d2844413090741c4d05168342509724343e13074cc17110d41c250f02c1411130743035040744c1d
|7=>0xc094101d092046037050744437090744c1d6d13c4411090741425051683425042b4145a0d0941c25050f84c1d0f1601c4d0d094305c05094101d09028101504074083c050444c1d04074343e130743425040744c1d180dc141d130943425090744c1d042b4145a0d09474350504410250c1681c110d094101d090f84c1d05454105a0d0941c5e05044142505044103e
|8=>0x4134341d090444c1d050943425090544c1f050f84c1d0c0dc101d05168342509074142502134141104134141d110541c25070443425050444c1d04054144d0504410250907410250702810150716834250c0d4101d130d4101d090d84c1d170dc14251316834251d130102507194744c0409425c10702810151104c241d130741c4d07094342504054103505095b435
|9=>0x50f84c1d0c054101d090744c1d110d41c25040544c35050744c25040541c25050d4104d170d41425040744c1d0713834270713434250405434270213414110713834250507414250d0f84c1d051343425040d41c25040543425040d44c1f090544c1d1104c241d040d4144d090f84c1d0709434250c05c101d11134241d110dc1c250713434250c134101d051683425
|10=>0x101d0d074141d041343425130d41c250513410150d09c3425040d41425180dc141d1707414250504414250213c1411040d4101d1713414250c094101d09024141105094101d1105c1c251113c241d090d44c1d04094141d0c09c101d17044142513094341d051343425130d41c251d0d41025
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x6440000604000000000005c41610000151000014100001310000121000011100000000404000000000000000f100000e100000d103040b100000a100000000000000024408101c406100000000000051000004100c4000000000000840000000011000000000040000000
|5,1=>0x8c400000002210844000000000008041f1078400007441c100000000000000000000000001b106840000000
|6,0=>0x444d0e342cc000420d053408cff33f0cf933d8cf333c0c0003b4c0003a8ce73390ce130000de336ccd83354cd230000000000000033cc000330cc93318c000000000000000000000c330000c032f4cba32dccb430000b132b8cab30000a83294ca2327cc9c3264c96324cc9030000000
|6,1=>0x6b4daa369cda43684d9e366cd983654d923000000000018f3630d893618d833600c0005f4d7a35dcd7435c4c0005b8d6b35a0d653588d5f3570d593558d533540d4d3528d473510d4134f8d3b34e0c0004d4d3234bcc0004b0d293498c00048cc000480c000474d1a300011730001143
|6,2=>0x20d3828e073810e0137f8dfb37e0df537c8def30001ec300000000001e93798c00078cde030001dd3768dd73750dd13738dcb3720dc53708dbf36f0db930001b636ccdb03
|7,0=>0xa38a8c2a28a882a18a842a08a8029f8a7c29e8a7829d8a7429c8a7029b8a6c29a8a682998a642988a602978a5c2968a582958a542948a502938a4c2928a482918a442908a4028f8a3c28e8a3828d8a3428c8a3028b8a2c28a8a282898a242888a202878a1c2868a182858a142848a102
|7,1=>0xa98aa42a88aa02a78a9c2a68a982a58a942a48a902
|8,0=>0xacc2b21ac46b01abc6ae1ab46ac1aac6aa1aa46a81
|9,0=>0x2b30
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 14 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x2000000000000000000100000200000000000000000000008000080000810000010000040002000000000000000000000000000000000000000000041000000000000000000000000000000000000080000010000000000000000000000000810001200000000004400000000080000000000100000000010000000040000000000000000001000000000000000000000000001000000044000000000080001000000000840000000010400000000000000000000000000240000000001000080000000000000000000006c0000000000400008000000000000000000000800000000000000020000000000000000200000000000
|6,0=>0x620011000043000bc000020000080000840400140000800001000000000000000010000000002c0004100008000020004008000000001800000b0002112000008000000000000004000b000080400201002188000610000042000000004220001000010000610800040001100020020071040004200000000c00000010004400020480000000000000080002040000000000880284000004800e40000000002000001000000000200000000008100002110001408004000000002bc00011000085000690000600000c08004020105400000000000040840000000007c000410002102002f00000000008800404000420800c400020000000000000000000000008000000000080020000840001040000000000000000000000000000000011000800000100008000148008424001890000000000000042080000200000000000000410002000011000210000090000a0400810082000084000000000000
|6,1=>0x1b080000000310003fc008424800000006100018c200000201242080100000000009000000000000000000004000008400000000080000900000000005200010c000010001082000008002000001100004000020000400008800002040018000000040110000800003f
|7,0=>0x210d0001f4400d4b001b08029900872008612200012c00040001940007c2008f4003f52000988002cb003b00070c020c7000b0c2007b50027f8000808029500057000b28001890000e4004464001d3000b70800bc000ff4800d4060840801f91002940014c2209600210c2007f4021f9000bd0000c40084618023c2007fc0003460184000188000c71102100807e004118200ab4001052003850027d0004742015d100290802fc0408c440020000530002502209c280068200316000940807e4001fc002d24802fd000570803b40003f
|8,0=>0xbf2003f4041dd0003d0902b92007f480bad200374882d5a003f4800bc2007f
|9,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 22 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_248,7,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 1 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 2 then [(dom_234,7,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 3 then [(dom_218,7,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 4 then [(dom_186,7,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 5 then [(dom_122,7,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 6 then [(dzo_242_8,6,runOps true dzo_242_8 (0,roots_242) ops)] else [])++(if pm.testBit 7 then [(dzo_234_16,6,runOps true dzo_234_16 (0,roots_234) ops)] else [])++(if pm.testBit 8 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 9 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 10 then [(dom_210,5,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 11 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 12 then [(dom_114,5,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 13 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 14 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 15 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 16 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])++(if pm.testBit 17 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 18 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 19 then [(dom_154,4,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 20 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])++(if pm.testBit 21 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_250 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_248 _ g hchk
    · exact cpcs (by decide +kernel) low_242 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_218 _ g hchk
    · exact cpcs (by decide +kernel) low_186 _ g hchk
    · exact cpcs (by decide +kernel) low_122 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_242_8_160 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_234_16_66 _ g hchk
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) low_226 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_240 _ g hchk
    · exact cpcs (by decide +kernel) low_216 _ g hchk
    · exact cpcs (by decide +kernel) low_168 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_82 _ g hchk
    · exact cpcs (by decide +kernel) low_58 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_248 7 s (0, roots_248) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_250 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_248 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_250 == dom_250) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_250 goalM v ys) : RunD true dom_250 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_250 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_12 : ∀ i, 12 ≤ i → i < 19 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 12 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 19 → Z 4 i = true := (range_split z4_0 z4_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_24 : ∀ i, 24 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_36 : ∀ i, 36 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_48 : ∀ i, 48 ≤ i → i < 60 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_60 : ∀ i, 60 ≤ i → i < 72 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_72 : ∀ i, 72 ≤ i → i < 84 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_84 : ∀ i, 84 ≤ i → i < 89 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 84 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 89 → Z 5 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split z5_0 z5_12) z5_24) z5_36) z5_48) z5_60) z5_72) z5_84)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_156 : ∀ i, 156 ≤ i → i < 167 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 156 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 167 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108) z6_120) z6_132) z6_144) z6_156)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_12 : ∀ i, 12 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_24 : ∀ i, 24 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_36 : ∀ i, 36 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_48 : ∀ i, 48 ≤ i → i < 60 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_60 : ∀ i, 60 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_72 : ∀ i, 72 ≤ i → i < 76 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 72 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 76 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_250 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_250 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_250 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_250 roots_250 goal_250 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_250

theorem low_250 : Lower true dom_250 roots_250 goal_250 10 := S_250.noCircuit

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

theorem low_233 : Lower true dom_233 roots_233 goal_233 8 :=
  lower_slice (d:=dom_233) (dSub:=dom_169) (T:=goal_233) (TSub:=goal_169) (roots:=roots_233) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000303000000000000000000000303000003030000000000000000, 1, 65)] (by decide +kernel) (by decide +kernel) low_169

theorem low_185 : Lower true dom_185 roots_185 goal_185 8 :=
  lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185) (TSub:=goal_169) (roots:=roots_185) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000303000000000000000000000303000003030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_169

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

theorem low_105 : Lower true dom_105 roots_105 goal_105 5 :=
  lower_slice (d:=dom_105) (dSub:=dom_41) (T:=goal_105) (TSub:=goal_41) (roots:=roots_105) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000000000000000, 1, 65)] (by decide +kernel) (by decide +kernel) low_41

theorem low_89 : Lower true dom_89 roots_89 goal_89 5 :=
  lower_slice (d:=dom_89) (dSub:=dom_81) (T:=goal_89) (TSub:=goal_81) (roots:=roots_89) (rootsSub:=roots_81)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30003000000000003000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_81

theorem low_57 : Lower true dom_57 roots_57 goal_57 5 :=
  lower_slice (d:=dom_57) (dSub:=dom_41) (T:=goal_57) (TSub:=goal_41) (roots:=roots_57) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_41

namespace S_121
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (1,65), (8,9), (8,40), (16,17), (16,80), (24,25), (24,56), (24,88), (32,33), (32,40), (48,49), (48,56), (48,112), (64,65), (64,80), (72,73), (72,88), (72,104), (96,97), (96,104), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_121.map (· &&& dom_121)
def goalM : Nat := goal_121 &&& dom_121
def NN : Nat → Nat
|3=>0x1
|4=>0x4
|5=>0xa
|6=>0x4
|7=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x1cc05
|4,0=>0x3852a3469003d4b03450
|5,0=>0x880a47c2605913139d472ba9c23f070d7a407776040c201ecf
|6,0=>0xa44c86922a1ebf3064ed
|7,0=>0xa44c8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x20002000200020002000200020002c0c0c0c0c0c0c0c0c0c0c0c000000000000000000000003030202030302020000000000000000c080c080c080c08000002000000020000000200000002c0c0c0c0c0c0c0c0c080c080c080c0b0302020303020203030202030302020000808000008080000080800000808000000000000000202020202020202c000c000c000c000c080c080c080c0b03030003030300030303000303030080808000808080008080800080808010101010101010101010101000000000000c0c00000c0c000000000000080b0303030303030302020202020202028080808080808080808080800000003030303030303030202020002020200c0c0c0c000000000c0c0c0c000000030003000300030003000300030003008080808080808080808080808080808000303000003030000030200000302c0c0c0c0c0c0c0c0000000000000003030303020202020303030302020202c0c00000c0c00000c0c00000c0c0003020302030203000302030203020300
|_,_=>0
def stPool : Nat → Nat
|0=>0xce131467098a3384c5c04c519ee3304e511cc12cac7304b6384c51d4673143419cb233827194d338cd22c4e1194cf19c262b42619cac31ca3584ca3a4e6095073146418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>0x26b48584cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 25 then fld (dictB (i / 512) (i / 32 % 16)) 122 (i % 32) else 0
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
|0=>0x31619d39590f095305095329195096095341196714099
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa2000000826242220200
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
|5,0=>0x280000870890cc0
|6,0=>0x3dffde
|7,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])++(if pm.testBit 1 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 2 then [(dom_89,5,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 3 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 4 then [(dom_81,4,runOps true dom_81 (0,roots_81) ops)] else [])++(if pm.testBit 5 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_121 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_113 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_89 _ g hchk
    · exact cpcs (by decide +kernel) low_57 _ g hchk
    · exact cpcs (by decide +kernel) low_81 _ g hchk
    · exact cpcs (by decide +kernel) low_41 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_113 5 s (0, roots_113) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_121 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_113 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_121 == dom_121) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_121 goalM v ys) : RunD true dom_121 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_121 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_121 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_121 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_121 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_121 roots_121 goal_121 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_121

theorem low_121 : Lower true dom_121 roots_121 goal_121 8 := S_121.noCircuit

namespace S_193
def pairsG : List (Nat × Nat) := [(1,65), (1,129), (64,65), (64,192), (128,129), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_193.map (· &&& dom_193)
def goalM : Nat := goal_193 &&& dom_193
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xf706
|3,0=>0xf706
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3000000000000000300000000000000000000000000000000c0000000000000000000000000000000c0000000000000002000000000000000200000000000000020000000000000002
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 194 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_193 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_193 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_193 == dom_193) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_193 goalM v ys) : RunD true dom_193 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_193 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_193 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_193 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_193 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_193 roots_193 goal_193 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_193

theorem low_193 : Lower true dom_193 roots_193 goal_193 4 := S_193.noCircuit

theorem low_225 : Lower true dom_225 roots_225 goal_225 5 :=
  lower_slice (d:=dom_225) (dSub:=dom_193) (T:=goal_225) (TSub:=goal_193) (roots:=roots_225) (rootsSub:=roots_193)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300000000000000030000000000000003000000000000000300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_193

theorem low_209 : Lower true dom_209 roots_209 goal_209 5 :=
  lower_slice (d:=dom_209) (dSub:=dom_193) (T:=goal_209) (TSub:=goal_193) (roots:=roots_209) (rootsSub:=roots_193)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30000000000000003000000000000000300000000000000030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_193

theorem low_177 : Lower true dom_177 roots_177 goal_177 5 :=
  lower_slice (d:=dom_177) (dSub:=dom_161) (T:=goal_177) (TSub:=goal_161) (roots:=roots_177) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300000003000000000000000000000003000000030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_161

namespace S_241
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (1,65), (1,129), (16,17), (16,80), (32,33), (32,160), (48,49), (48,112), (48,176), (64,65), (64,80), (64,192), (96,97), (96,112), (96,224), (128,129), (128,160), (128,192), (144,145), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_241.map (· &&& dom_241)
def goalM : Nat := goal_241 &&& dom_241
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xfe82e
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3000300030003000300030003000300000000000000000000000000000000c000c000c000c0000000000000000000c000c000c000c0000000000000003000300000000000300030000000000030003000000000003000300000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0002000200020002000200020002000200020002000200020002000200020002
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 242 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_225,5,runOps true dom_225 (0,roots_225) ops)] else [])++(if pm.testBit 1 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 2 then [(dom_177,5,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 3 then [(dom_113,5,runOps true dom_113 (0,roots_113) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_241 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_225 _ g hchk
    · exact cpcs (by decide +kernel) low_209 _ g hchk
    · exact cpcs (by decide +kernel) low_177 _ g hchk
    · exact cpcs (by decide +kernel) low_113 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_225 5 s (0, roots_225) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_241 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_225 h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xffffffffffffffff0000000000000000, 64)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_241 == dom_241) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_241 goalM v ys) : RunD true dom_241 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_241 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_241 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_241 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_241 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_241 roots_241 goal_241 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_241

theorem low_241 : Lower true dom_241 roots_241 goal_241 7 := S_241.noCircuit

theorem low_201 : Lower true dom_201 roots_201 goal_201 5 :=
  lower_slice (d:=dom_201) (dSub:=dom_193) (T:=goal_201) (TSub:=goal_193) (roots:=roots_201) (rootsSub:=roots_193)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300000000000000030000000000000003000000000000000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_193

theorem low_153 : Lower true dom_153 roots_153 goal_153 5 :=
  lower_slice (d:=dom_153) (dSub:=dom_137) (T:=goal_153) (TSub:=goal_137) (roots:=roots_153) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000000000000000000003030000, 1, 17)] (by decide +kernel) (by decide +kernel) low_137

namespace S_217
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,65), (1,129), (8,9), (8,136), (16,17), (16,80), (24,25), (24,88), (24,152), (64,65), (64,80), (64,192), (72,73), (72,88), (72,200), (128,129), (128,136), (128,192), (144,145), (144,152), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_217.map (· &&& dom_217)
def goalM : Nat := goal_217 &&& dom_217
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xd6b6a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3030303000000000303030300000000000000000000000000000000c0c0c0c0000000000000000000000000c0c0c0c0000000000000003030000000000000303000000000000030300000000000003030000c000c00000000000c000c00000000000c000c00000000000c000c02020202000000000202020200000000020202020000000002020202
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 218 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 1 then [(dom_201,5,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 2 then [(dom_153,5,runOps true dom_153 (0,roots_153) ops)] else [])++(if pm.testBit 3 then [(dom_89,5,runOps true dom_89 (0,roots_89) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_217 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_209 _ g hchk
    · exact cpcs (by decide +kernel) low_201 _ g hchk
    · exact cpcs (by decide +kernel) low_153 _ g hchk
    · exact cpcs (by decide +kernel) low_89 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_209 5 s (0, roots_209) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_217 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_209 h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffffffffffffffff0000000000000000, 64)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_217 == dom_217) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_217 goalM v ys) : RunD true dom_217 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_217 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_217 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_217 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_217 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_217 roots_217 goal_217 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_217

theorem low_217 : Lower true dom_217 roots_217 goal_217 7 := S_217.noCircuit

namespace S_249
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (1,65), (1,129), (8,9), (8,40), (8,136), (16,17), (16,80), (24,25), (24,56), (24,88), (24,152), (32,33), (32,40), (32,160), (48,49), (48,56), (48,112), (48,176), (64,65), (64,80), (64,192), (72,73), (72,88), (72,104), (72,200), (96,97), (96,104), (96,112), (96,224), (128,129), (128,136), (128,160), (128,192), (144,145), (144,152), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_249.map (· &&& dom_249)
def goalM : Nat := goal_249 &&& dom_249
def NN : Nat → Nat
|6=>0x1
|7=>0x5
|8=>0x2
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xbdd1b
|7,0=>0x465234331d367661df6d02981
|8,0=>0x70ec86c8ea
|9,0=>0x64311
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x30303030302030203030303030203020303030303020302030303030302030200000000c080c08000000000c080c08000000000c080c08000000000c080c0b03030300000000030303030000000003030303000000000303030300000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c0202020202020202020202020202020202020202020202020202020202020202c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000000000000000000303030303030303000000000000000003030303030303030000000000000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c000302030203020302030203020302030203020302030203020302030203020302c0c0c0c080808080c0c0c0c080808080c0c0c0c080808080c0c0c0c0808080b03030303000300030303030300030003030303030003000303030303000300
|_,_=>0
def stPool : Nat → Nat
|0=>0x5483765483762543687054372815437682a543768a54376895436170543210
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x6
|7,0=>0x2376e14735c67
|8,0=>0xc5ea7
|9,0=>0x386
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 11 then fld (dictB (i / 512) (i / 32 % 16)) 250 (i % 32) else 0
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
|0=>0x1d98761976609766097660a765e18661d865d9
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x3
|7,0=>0xb292725232
|8,0=>0xe1d1
|9,0=>0xf0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|6,0=>0x3f
|7,0=>0x1bff07bd4f7f
|8,0=>0x17e7f
|9,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 9 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_233,8,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 1 then [(dom_185,8,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 2 then [(dom_121,8,runOps true dom_121 (0,roots_121) ops)] else [])++(if pm.testBit 3 then [(dom_248,7,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 4 then [(dom_241,7,runOps true dom_241 (0,roots_241) ops)] else [])++(if pm.testBit 5 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 6 then [(dom_209,5,runOps true dom_209 (0,roots_209) ops)] else [])++(if pm.testBit 7 then [(dom_240,4,runOps true dom_240 (0,roots_240) ops)] else [])++(if pm.testBit 8 then [(dom_216,4,runOps true dom_216 (0,roots_216) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_249 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_233 _ g hchk
    · exact cpcs (by decide +kernel) low_185 _ g hchk
    · exact cpcs (by decide +kernel) low_121 _ g hchk
    · exact cpcs (by decide +kernel) low_248 _ g hchk
    · exact cpcs (by decide +kernel) low_241 _ g hchk
    · exact cpcs (by decide +kernel) low_217 _ g hchk
    · exact cpcs (by decide +kernel) low_209 _ g hchk
    · exact cpcs (by decide +kernel) low_240 _ g hchk
    · exact cpcs (by decide +kernel) low_216 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_233 8 s (0, roots_233) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_249 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_233 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_249 == dom_249) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_249 goalM v ys) : RunD true dom_249 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_249 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 2 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_249 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_249 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_249 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_249 roots_249 goal_249 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_249

theorem low_249 : Lower true dom_249 roots_249 goal_249 10 := S_249.noCircuit

theorem low_171 : Lower true dom_171 roots_171 goal_171 8 :=
  lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171) (TSub:=goal_169) (roots:=roots_171) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c000000000000000000000c0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) low_169

theorem low_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_slice (d:=dom_195) (dSub:=dom_194) (T:=goal_195) (TSub:=goal_194) (roots:=roots_195) (rootsSub:=roots_194)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000000000000000a000000000000000a000000000000000a, 64, 65)] (by decide +kernel) (by decide +kernel) low_194

theorem low_139 : Lower true dom_139 roots_139 goal_139 5 :=
  lower_slice (d:=dom_139) (dSub:=dom_137) (T:=goal_139) (TSub:=goal_137) (roots:=roots_139) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000000000000000000000000000c0c, 128, 130)] (by decide +kernel) (by decide +kernel) low_137

namespace S_203
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (2,66), (2,130), (3,11), (3,67), (3,131), (8,9), (8,136), (10,11), (10,74), (10,138), (64,65), (64,66), (64,192), (72,73), (72,74), (72,200), (128,129), (128,130), (128,136), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_203.map (· &&& dom_203)
def goalM : Nat := goal_203 &&& dom_203
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0x6b015
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0000000000000f0f00000000000000000000000000000000f0f00000000000000000000000000000f0f0000000000000000f000000000000000f000000000000000f000000000000000f00c0c0000000000000c0c0000000000000c0c0000000000000c0ca0a0000000000000a0a0000000000000a0a0000000000000a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 204 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 1 then [(dom_201,5,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 2 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 3 then [(dom_139,5,runOps true dom_139 (0,roots_139) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_203 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_201 _ g hchk
    · exact cpcs (by decide +kernel) low_195 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_202 5 s (0, roots_202) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_203 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_202 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_203 == dom_203) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_203 goalM v ys) : RunD true dom_203 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_203 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
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

theorem low_227 : Lower true dom_227 roots_227 goal_227 6 :=
  lower_slice (d:=dom_227) (dSub:=dom_226) (T:=goal_227) (TSub:=goal_226) (roots:=roots_227) (rootsSub:=roots_226)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a, 32, 33)] (by decide +kernel) (by decide +kernel) low_226

theorem low_107 : Lower true dom_107 roots_107 goal_107 6 :=
  lower_slice (d:=dom_107) (dSub:=dom_105) (T:=goal_107) (TSub:=goal_105) (roots:=roots_107) (rootsSub:=roots_105)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) low_105

theorem low_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_slice (d:=dom_163) (dSub:=dom_162) (T:=goal_163) (TSub:=goal_162) (roots:=roots_163) (rootsSub:=roots_162)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0000000a00000000000000000000000a0000000a, 32, 33)] (by decide +kernel) (by decide +kernel) low_162

theorem low_43 : Lower true dom_43 roots_43 goal_43 5 :=
  lower_slice (d:=dom_43) (dSub:=dom_41) (T:=goal_43) (TSub:=goal_41) (roots:=roots_43) (rootsSub:=roots_41)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) low_41

namespace S_75
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,66), (3,11), (3,67), (8,9), (10,11), (10,74), (64,65), (64,66), (72,73), (72,74)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_75.map (· &&& dom_75)
def goalM : Nat := goal_75 &&& dom_75
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x637f2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0000000000000000f000000000000000f00c0c0000000000000c0ca0a0000000000000a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 76 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_75 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_75 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_75 == dom_75) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_75 goalM v ys) : RunD true dom_75 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_75 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_75 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_75 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_75 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_75 roots_75 goal_75 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_75

theorem low_75 : Lower true dom_75 roots_75 goal_75 4 := S_75.noCircuit

namespace S_235
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (1,129), (2,34), (2,66), (2,130), (3,11), (3,35), (3,67), (3,131), (8,9), (8,40), (8,136), (10,11), (10,42), (10,74), (10,138), (32,33), (32,34), (32,40), (32,160), (64,65), (64,66), (64,192), (72,73), (72,74), (72,104), (72,200), (96,97), (96,98), (96,104), (96,224), (128,129), (128,130), (128,136), (128,160), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_235.map (· &&& dom_235)
def goalM : Nat := goal_235 &&& dom_235
def NN : Nat → Nat
|3=>0x2
|4=>0x24
|5=>0x84
|6=>0x93
|7=>0x35
|8=>0xa
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x690611d66d
|4,0=>0xfb09eccb34c4064bbf6ab71d8b13c99f6a6978cc939db8c66a8456382b2f7a992707b46e64a69d3069ce769b7a662595c4014fd8b4f45446f333fc822a5f527c292228c20c011d4c9148c0145fb13a900e1a3093930915401acb
|5,0=>0xd5523d4c71cf260cbee8c59a4b92a5b57c6b1b6da9076a8b48a81c3a3cc9a33b3a20ba9fc459f1a99cc579a4959a1de969cd950be91fda9112c8fb938a6cb8a601852e7835fb82897804d77ca5678d267888b77ef075da472cd071bc46cad36bca86ac40672b26469b645e26425961f1c613ad613285e0845da3959f4c599f557cd955f8a544d7534985332d52f4352ec952358504ac4f3b44d3454a2b54840247d0c417bf40cf540ac53fd253f6513e4543c56c3c22b3c1233a8d93a614396c63923f3908c3803d36c4b333923296130c6c300882ef362ea122ddf52c98f2c75d2be6f2b6d02b1a22a0832648e250b224ab524656237f02352422c221df0e1dec11cb4f1aa851a6fe1a3a819c1c189d417a9116ff616182149b2141b10efe20eae509e2309c6d0926708ff4077cd0513004ebf03d0703b9a026390192800279
|5,1=>0xf3f74dea82da333d9ca2
|6,0=>0xa3dfaa3c8da3a5aa2d80a0c929e53f9df709b5539b33a974f696647959898df948c3508a5fb88750873c683be78392c8251181cf27c6bc7b12f79d9578926779e5764c57435373ebb724c871d38701596f5436f3536e5cb6ce4d6bfdb69280683e867e3266293657a56544f5f9715f258574355560e54a19542b253e0e52874505875009c4f9314f46b4d9284c9cf4b88e4aace4916948c3b4854748402482b647f26470d943f2743dbc434a6433ed4254e414383fc353fae83daaa362213568d351b1347003410b337b03230f2fc862e0192ae332a6f4296af27ab72707326a8d25b2f246eb236ee22ca720705202451f8d01f3071e1d91d3b81c8b71c7861c5811c1781b8971b84d1b2591a4f7195fd17ada16d8716a5013bdc12d4611f7710e8e0ef6b0dc7d0d6df0ccf00ad33083b0070f20434c041de01f59012d200aec
|6,1=>0xfe177f27f5ed092e5a0ed97b9cbf62c6414c0104bfb35bcc42bc9e6b7f2eb4aa5b281ab1ab1ac3cfa9002a8164a5223
|7,0=>0xf895bddb9dd61cfc7baac2d9abf3faba5eab6b43b58b7a13c587d9687c6b870b285e8182c4c82bc7820d77a4a07868e77f4271d4b6d0f26c301674f1646a45a124535b9522ef51ba44b273471f3462a343b4d3933037b4c372cf355732f0362ed262e0872277019ef218a1915f501528b13d0512d25125bb10710106620d8880c2a509373
|8,0=>0xea0aaad97b99ba570229559aa41b293ced03c0df372cf028b1
|9,0=>0xd268f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x5050000050500000505000005050000050000000500000005000000050000000000f0f0000000000000f0f0000000000000f000000000000000f00f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0a00000f0af0e00000f0e00000f0e00000f0e00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000a0a00000f0f0000000000000f0f00000000f0f00000a0f00000f0f00000a0f00000f0f00000a0a00000f0f00000a0af0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000a0a00000000000000000000000000000000f0f00000e0e00000f0f00000e0ef0f00000a0a00000f0f00000a0a00000f0f00000a0a00000f0f00000a0ae0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000000f0f00000f0f00000f0f00000f0a00000f0f00000f0f0000000000000000f0f00000f0000000f0f00000f0000000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0c00000c0c00000c0c00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000f0f00000f0e00000f0f00000f0e00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0a00000a0a00000a0a00000a0a00000a0a00f0000000f0000000f0000000f00000000000000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000f0f00000a0ac0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000e0e00000c0c00000c0c00000c0c00000c0cf000000000000000f0000000f0000000f000000000000000f0000000a00f0f00000f0f00000f0f00000f0f00000000000000000000000000000000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ef0000000a0000000f0000000f0000000f0000000a0000000f0000000a00
|0,1=>0xf000000000000000f000000000000000000000000000000001010000010100000101000001010000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00000f0f00000a0af0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000f0e00000000000000000000000000000000f0f00000f0f00000f0f00000f0050500000505000005050000050500000504000005040000050400000504f0f0000010100000f0f0000010100000f0f0000000000000f0f00000000a0f00000a0f00000a0f00000a0f00000a0f00000a0a00000a0f00000a0a101000001010000010100000101000001010000000000000101000000000000000000000000e0e00000f0f000000000000000000000e0e00000e0e00f0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000f000000000000000f000000000000000f000000000000000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0000000f0f00000f00f0f00000f0f00000f0f00000f0000000f0f00000f0f00000f0f00000f00000000000000000000000000f0f00000000000000000000000000000f00f0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000f0000000000f050000000000000f050000000000000f000000000000000f0000f0000000f0000000f0000000f0000000f000000000000000f00000000f0f00000f0f00000f0f0000000000000e0e00000e0e00000e0e0000000000000000505000000000000050500000000000005000000000000000500f0000000f0000000f0000000f0000000f0000000e0000000f0000000e0010100000101000001010000010100000101000001010000010100000000f0f00000f0f00000f0f00000f0a00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000e0e00000f0f00000f0f0000000000000000f0f0000000000000f0f00000f0f00000f0f0000000000000f0f0000000000000000f0f0000000000000f0f0000000000000f0f0000000000000a0aa0f00000a0f00000a0f00000a0f00000a0a00000a0a00000a0a00000a0af0000000f0000000f0000000f0000000f0000000a0000000f0000000a00f0f00000f0f00000f0f00000a0a00000f0f00000f0f00000f0f00000a0af0000000b0000000f0000000b0000000f0000000a0000000f0000000a00f0f00000a0a00000f0f00000f0f00000f0f00000a0a00000f0f00000a0a00f0000000f0000000f0000000f0000000f0000000a0000000f0000000a
|0,2=>0xf0f0000000000000f0f0000000f00000f0f0000000000000f0f0000000050500000505000005050000050500000000000000000000000000000000f0f0000050500000f0f0000050500000f0f0000000000000f0f0000000000000000000000000000000000a00000a0a00000a0a00000a0a00000a0a00000000000000000000000050000000f0000000f0000000f0000000f0000000000f0f0000000000000f0a0000000000000f0f0000000000000f0aa0a00000a0a00000a0a00000f0f00000a0a00000a0a00000a0a00000a0a00000000f000000000000000f0f0000000000000f000000000000000f0030300000303000003030000030300000303000003030000030300000202f0f0000000000000f0f00000f0f00000f0f0000000000000f0f00000e0eb0b00000b0b00000b0b00000b0b00000b0b00000a0a00000b0b00000a0a0000000000000000f0f00000f0f000000000000000000000e0e00000e0e00000000f0f0000000000000f0f0000000000000f0a0000000000000f0af0f00000f0a00000f0f00000f0a00000000000000000000000000000000a0a00000b0b00000a0a00000b0b00000a0a00000a0a00000a0a00000a0af0f00000e0e00000f0f00000e0e00000f0f00000e0e00000f0f00000e0ef0f00000e0e00000f0f00000e0e00000000000000000000000000000000f0f00000f0f00000f0f00000f0000000f0f0000000000000f0f00000000f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0ef0f00000f0f00000f0f00000f0f00000f0f00000e0e00000f0f00000e0e3030000030300000303000003030000030300000303000003030000000000000000f0f0000000000000f0f0000000000000a0a0000000000000a0af0f00000f0f00000f0f00000a0a00000000000000000000000000000000f0e00000f0e00000f0e00000f0e00000000000000000000000000000000f0f00000f0f00000f0f00000f0f00000f0a00000f0a00000f0a00000f0a00000000f0f0000000000000f0f00000000000000000000000000000000a0a00000f0f00000a0a00000f0f00000a0a00000a0a00000a0a00000a0a50500000505000005050000050000000505000005050000050500000500f0f00000f0f00000f0f00000f0000000000000000000000000000000000f0f00000f0a00000f0f00000f0a00000f0f00000f0a00000f0f00000f0a00f0000000f0000000f0000000f0000000a0000000a0000000a0000000ab0b00000b0b00000b0b00000b0b00000a0a00000a0a00000a0a00000a0a
|0,3=>0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000000000000000000000000f00000000000000000000000000000000f0f0000000f00000f0f0000000f00000f0f0000000a00000f0f0000000a5050000050500000505000005050000050500000500000005050000050000500000005000000050000000500000000000000000000000000000000f0000000f0000000f0000000f0f00000f0000000f0000000f0000000f00f0000000f0f00000f0000000f0f00000f0000000f0000000f0000000f00000000000000000000000000f0f0000000000000000000000000000000000500000005000000050000000500000005000000000000000500000000f0f00000f0f00000f0f00000f0f00000f0f00000f0a00000f0f00000f0a00000000000000000000000000000000f0f00000f0a00000f0f00000f0a00f0000000f0000000f0000000f0000000e0000000e0000000e0000000e00f0000000e0000000f0000000e0000000f0000000e0000000f0000000ef0f0000000f00000f0f0000000f00000f0f0000000000000f0f0000000000000000000000000000000050500000000000000000000000000000000f0f00000f0f00000f0f0000000f00000f0f00000f0f00000f0f00000000f0500000f0500000f0500000f0500000f0500000f0000000f0500000f00303000003030000030300000303000003030000030300000303000003005050000050500000505000005050000050500000505000005050000050050500000505000005050000050500000505000000000000050500000000f0f00000f0f00000f0f00000e0e00000f0f00000f0f00000f0f00000e0e5050000050500000505000004040000050500000505000005050000040400f0000000f0000000f0000000f0000000f0000000f0000000f0000000aa0a00000a0f00000a0a00000a0f00000a0a00000a0a00000a0a00000a0af0500000f0500000f0500000f0500000f0000000f0000000f0000000f00f0f0000000f00000f0f0000000f00000f0f0000000f00000f0f00000000a0a00000f0f00000a0a00000f0f00000a0a00000f0a00000a0a00000f0af0100000f0100000f0100000f0100000f0000000f0000000f0000000f005000000050000000500000005000000050000000500000005000000050030300000303000003030000000300000303000003030000030300000000f0f0000000000000f0f0000000000000f0e0000000000000f0e0000000050500000505000005050000050500000505000005050000050500000000
|0,4=>0xf0f00000f0f00000f0000000f0000000f0f00000f0f0000000000000000a0f00000a0f00000a0f00000a0f0000000000000000000000000000000000a0000000a0000000a0000000a00000a0a00000a0a00000a0a00000a0a00000000000000000000000000000000f0000000f0000000f0000000f00f0a00000f0f00000f0a00000f0f00000f0a00000f0a00000f0a00000f0af0f00000f0f00000f0f00000f0f00000500000005000000050000000500f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f00000000005050000000000000505000000000000000000000000000000005000000050500000500000005050000050000000500000005000000050000000000005000000000000000500000000000000000000000000000000f0a00000f0a00000f0a00000f0a00000a0a00000a0a00000a0a00000a0ae0e00000f0f00000e0e00000f0f00000e0e00000e0e00000e0e00000e0ef0000000f0500000f0000000f0500000f0000000f0000000f0000000f00f0000000f0000000f0000000f000000000000000000000000000000000000f0000000f0000000f0000000f00000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0a00000f0f00000f0f00000f0f00000f0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x1030d022409080323160e0301082209030221010103020b200212091f010a021e1d0d06080709130a120902100e08011c0c0a09021b0d0103091a020901030219090d01180209030217160a0908150d0e010c140b06120902130e060112110a08020c1001090f0b0201090c0b020a0306020409080706050103020403020100
|1=>0x206210a021209061f0a06030235340a0e0333171d0a090807230d0308093223010a06030902300e0103080b200e01091f08120a020306092f0e010d08092e0e0a1d0d081e0103020b24090601122d0103092c02060301022b0903022a170a12060229010302240a08070910090d0801280902270d0109030201260212092501
|2=>0xa0e08420d0c0a0e171209410a09030206260903014008020e010d08093f0a02120906250906013e12020a091206023d0e01092508120a0203060d240e010d0908330e080d013c0c0a061209023b0e080301093a09010d12020906030139020e01030809380e01030d08240a08020c1d0d0902030601370906030801360a0903
|3=>0x803510608020903130e06010803110e010308240a02120c061d0e090d08014f0a060309024e090802070d01090603014c0206030209344b0e01090c084a0a090802490d0e011703092e0e080601480c0e0a094712170a0203091d0b0a090227060d0e01090c0845030a020944170a02030925170a06120902430903013e1702
|4=>0x60301082b0a0e140c065d0a0e0908520d0a080209035c0a080206035b010d090c0802030a0209065a0a0212091d0d0a09030259170a06030209580908030206570e0a060803200e01030933170a02030c1d170906030108560a0e14030b1d0908030206160e09030801550903010817540a02030906530e0a0608520c0e0901
|5=>0x660a02030906650e0803016463030a02321d170a08020903100906010318020a06080709430608030902620a090608031509031202230109010d0312020e0a1d080b0c0e0a1d0d14120903020717010e06030109610a0e09420d120e090d0150120e010309082c0906034d50020a09030260170a060209035f010d090f08020e
|6=>0x2508020e01090f080b0e01031f08140e01090c080b0a080302096d0a0e140c066c0a0e171209250a09080706490e09013e171203090802016a0a0e141206670e0103080b240a090306021b0a08030206690103091f08020301093c17020e01090803680103090f17020e01030d08200a02120609670103090c17020a06030209
|7=>0xe030806096f0a0e08140c060d0a0903020706170e080a030d091f0a0e091403066c0e09010d03081208090603014d540901030b020906010803280a02090f0d170e010309081a0a02090c0d1709080302062a0901030d0b020e01091f08460e0a064712140a0902070d170e0a1d17120c06080302096e030802094401010309
|8=>0x6010809730e0906014d081203090117020e090103084a0e0803013e09630e0103090c08170e080a0d090c1f0e0a091d1703120e0601090f08120e09010308450e0a09064708460a0e03090806650e0601090c08120a0e06170309720a0608030709320a0908020603710a0608030902700e0906010803180a0903120602230a
|9=>0x8120a06080302097a0a0e09080306680e0601030809790e08010d090f0a0903027806170a0e080333061d0a0e08090c066c030e01093c08170e0a03060d08200e08010d090c0e0a09060308770e0a09060803760a0e091406030b0e0103090f08170a060203090c1e0e0a09060803750a0e08120609670e080603010974030e
|10=>0x2310a090212065e090603013e08020a0e081403061f0e0a08060b090c0a0e091412060d0e0a06094108120309080223010a06080209033b0309080602016b0901030d08020a0e090803067c06090803024b0e0a0806030b240a0e140617030c0e090a170d120e080a1d0d030c0a060e14030c1e0a08020309061f0e0a09067b
|11=>0xa060e14120c030a0802090680030a0217091d0e0a09034708170a0908030706230a09080302067f0a0608020903430a06080209037e0e0a091d0308450e0a030609087d0e06010308092e0e0a09064708120e0a0817030941030a08020906440a0802030906250a0603020709340e0a080603200e0a08060b090f0a06080309
|12=>0xe0a08170d090f0a0e08850c0e08010d03090c0e0906030801840e0a060842030c0e0a08170d090c0a090203060d0b0e06010908033f0a0908030206590a0e084609061f0e0901030d080b030a0e14171d0e0a08060309830a09080207065e0e0601030908330e0806013c030c0e080103091f0a0802030c061d0e080a060c81
|13=>0x30209890e0a080688090c0a0e08140c065e030a080232061d0e090103080b0a0e03080906870e0a1d030d08140a0602031209330a0e090842030d0e0a09060803860e090a170d03120a0802090c065e090803020706010e08030d09013c0a0908020603490e0a080603091a0e08010309250a0908030206600a0802091d030d
|14=>0x9200a0e08120906250a0e08140306670e0906013e08120e0a03060d08240e0a091d0d08460e09010d08120e0906015003120e090603080137030601093c0802030a08093206230e0a0806030b200a0e081209061f0e080109038a080203090f06010a06090302270e0a0906080352080203090c06010a02031206091d0a0608
|15=>0x906250a060e0308092e0a0e0803098d0e08090603013e0e080a068c0f0e080a060d03090c0a090e0308066c030e080109630e080901030d0e080a03090c06470e090a03060d080b0e0a080603092c0e080a06810a060234030c0a060e0903331e0e0a080603240a0e080645090c0e0a090603088b0a090217030d0e0a080603
|16=>0x90c061f0e090a0817030d0a060e0309081e0e080a065e090c0e090a060d08120a060908030207030a0e091406170e080a091d030d0e080a0906038a0309080206010a060e0908033f0e080a0609030c0e0a09061d0308120e080a061d030c0a060e090803330e090a0806030b0a060e03081209330e090a060d08460e080a03
|17=>0xa08061703090c0a090e03080645030e090108170e090a060d0308120e080a06820c080a0603098f0a060e0834030c030e0a061d0814030e0a09060842030e09060108500e090a080603880e080a0906038e0e080a03060967030e080601093c030a080209061d0a09080203065e0a06080203090f0a06080203090c0e080a03
|18=>0x30e08090a060e080a060309820e08090a03060d030a060e0908340e080a0603098c030e090a080617030e080a09061d0e08090a03065e0e080a0603090f0e080a0603090c030a060908020a0e09081403065e0a09080203060d0a0e080309850e080a060d090f0e080a060d090c0e0a08061703090f0e
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x440004
|4,0=>0xb650b150ac50a750a2509d50994094508f508a50855080507b50765071506c50675062505d50585053504e50495044503f503a50355030502b50265021501c50175012500d50085
|5,0=>0x233622d62276221621b6215620f6209620361fd61f761f161ec51e661e061da61d461ce61c861c261bc61b661b061aa61a4619e61986192618c61866180617a6174616e61686162615c61566150614a6144613e61386132612c61275121611b6115610f6109610360fd60f760f160eb60e560df60d960d360cd60c760c160bb6
|5,1=>0x3b363ad63a763a1639b6395638f63896383637d63776371636b6365635f63596353634d63476341633b6335632f63296323631d63176311630b630562ff62f962f362ed62e762e162db62d562cf62c962c362bd62b762b162ab62a5629f62996293628d62876281627b6275626f62696263625d62576251624b6245623f62396
|5,2=>0x3cb53c563bf63b96
|6,0=>0x57e75786571756a7563755c7555754f65487541753b6534752e65277520751a6513750c750574fe74f774f074e974e364dc74d574ce74c774c074ba64b374ac74a5749e7497749074897482747b7474746f54696462745b7454744d7446744064397432742b7424741d7416740f7408740173fa73f373ec73e573de73d773d07
|6,1=>0x732772b7725671e77186711770a770376fc76f576ee76e776e166da76d376cc76c576be76b776b076a976a2769b7694768e6687768076797674566d7666765f76587651764a7643763c7635762f66287621761a7613760d6606760065fa65f375ed65e675df75d875d175ca75c375bc75b575ae75a775a075997592758c65857
|6,2=>0x7b177ac57a6679f77996792778b7785677e7777777077697762775b7755674e7747774077397
|7,0=>0x924891d791769107909790188f988f278ec68e488de68d868d178ca78c378bc78b578ae78a778a078997892788b7884787c8875786e7867786078597852784b7844783e6837783078288821781a7813780b880477fd77f677f067e977e367db87d477ce67c867c087b88
|8,0=>0x96a7963795c7955794e7947794079397932792c6
|9,0=>0x9716
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 144 then fld (dictB (i / 512) (i / 32 % 16)) 236 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 8 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 16 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 1 zs)
def opPool : Nat → Nat
|0=>0x30641851090842c240d0840c190e0843021030940c190a0640c25090140c190a0640c19090640c250e0841825080640c51090840c19020640c090e08428190602408250e08420c50c02c0c250e0842c270d0840c190a0642c240e08434210306428190b09c38210d0840c190a0643421080940c250306428190e08434210309c0c190a06438210d0840c25030642819
|1=>0x90640c250e0842419031741821090841c040a0640c090e0840c25034202075090642c240d0840c190a0641825030940c210e0840d40080140c190a0642819030640c090e08438214d0840c050a0643423030940c190a0640c190323008190e0842019030840c75090644819060940c210e08419190308c0c250a0640cc8090240c210e0843821080640c070a0640c25
|2=>0x60840c270a0643821060840c250a06420190609408250e08438210350804210a0642819060240c210e0843821030840c190a0640c25031742019090640c21080940c19090642819080640c090e0840c21030641851090840c21080140c190a06421790306c0c25090840c19034201851090843821030940c190a0640c19060940c210e08420190c0840c250a0642019
|3=>0x4d0ec0c050a06438210d0840c190a0641821030640c250e08438210d0840c190a0642025030840c75090641821030640c090e0840c250308420190906428190632808250e08434210309c0c190a0643421030940c190a064183d0309c0c21060840c8c020640c090e085ac1b0201428190e08425790306c0c210908438210c06c0c250a06438210806404250a0643821
|4=>0xa0654027010842819030840c050a06438210608428190d08c0c190a064241b0301c2819060840c250a064301b030940c19030842019090640c210309c2819064640c230a0640c21030942819080f40c27060840825030243821020f40c270e0840d42010842819060240c210e0840c19030942421080640c090e0851c1b0d0940c191206c0c21090840c21030642819
|5=>0x30642819070ac0c090e0840c25060842421030840c19080640c250306424190c08c0c2509084301b030943821030840c770906425e10302c3821094640c230a0640c27030642819060840c0b0e08424190314424211206c0c250308420190109428190b09c3421030640c250306428190317418210908418210309c28190c08c0c250e08425790306c0c214d09c0c05
|6=>0x70640c090e0840cc8020943821064640c230906421050d09c0c191209c0c210a0640c21031d424190d09c0c190806418ca020943821060f40c270e08420260302438210b09c0c5d080640c270317420190306c0c210e08438210301c28190c06c0c25090840c25031742019030640c21090840c210d09c0c190a06408190e0840cca0209438210201428190e0843821
|7=>0xe0840c27030642019030941a09030900c25030642819014640c230a0640c25081d42419030940c190806434210306438210314c24210a06419e10302c38210d0840c190a06424190608424210306c0c090e08430210309428190309404250a064301b030942819090640c250e084320b030940c24030940c21090841825080643821060840c75090640819030243821
|8=>0x309c3821087840c0b0e0840d08081d424190a0640c250e0841825030843821070940c090e0840c250317c20190306c0c250908418250209438210d0840c190a0642025030642419120940c210e0840c19061442421030840c19080640c1b0309438210a0640c090e08424050306428190323008190e0845c3d0309c2019060f40c270a0641c1b030243821030642419
|9=>0x308418260a0640c190a064301903094342103064320b030940c240309420260e084cc230314424210b0900c5d080640c25064640c230306420190e084183d0309c0c21095e40c1b090840c210301c28190b0903421030640c23030642419030840c190a0640c210108428190e08404250a06418090209438210b09c0c5d08064301b030940c210363418260a0642819
|10=>0x80640d8f0906c25790306c04250a06424190e0840c1b0e0840c270e0840c250e084301b030940c19080643023030940c250306c0c21030640c090e0841821090840c19090640d8d0906c28190e0840c53090840e31030980c21090640c25090640c51090840c5d080644825030840c2303064183d0309c4827030841a0b030900c070a0640c27030980c2503064481b
|11=>0xc24030642423030982019090640c1b0309c0c250e0840c1b090840c190e0841a09030900c27030640c25030640c27080640c250806419190308c18210a0640c21030640c25030903a09030900c250908c20250906420750906404210a0640c5f
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x514000000000000000000000000000000003d4000000000000000000000000000000000000000294000000000001540050000000
|5,0=>0x20507d400007941d5000000000001c5000000000001b50694195000018505d400005941550000000051413500001250000000045410503d400000000000000000000000000000e503540c500000000000000000000002d40000000000000000002940950214075019400000000000000
|5,1=>0x3d500003c500003b50e9439500003850000375000036500000000d5434500003350c9400000000000c5430500002f500000000b9400000000000b540000b1400000000000ad42a50a5428509d40000994255000000000000000000000091423500000000894000085400000000000000
|5,2=>0x3e500000000000
|6,0=>0x1993658d933640d8d3628d873610d8135f8c0005ecc0005e0d7535c8d6f35b0d693598c00058cd603574d5a355cd543544d4e3000000052cd483514c000508d3f34f0d3934d8d3334c0d2d34a8d273490d2130000000478d1b3460c000454d12343cc000430d093418d033400cfd3
|6,1=>0x91ce443904e3e38ece3838d4e3238bce2c38a4e26388cc000880e1d3868c00085ce143844e0e382ce083814e0237fcdfc37e4df637ccdf037b4dea379cde430001e13778c00076cdd83754dd2373cdcc3724c000718dc33700dbd36e8c0006dcdb436c4dae36acda83694da2367cd9c3
|6,2=>0x9d0e7139b8e6b39a0c000994c000988e5f3970e593958e533940c000934e4a3
|7,0=>0x2df2b74adb2b64ad72b54ad32b44acf2b34acb2b24ac72b14ac32b04abf2af4abb2ae4ab72ad4ab32ac4aaf2ab4aab2aa4aa72a94aa32a84a9f2a74a9b2a64a972a54a932a44a8f2a34a8b2a24a872a14a832a04a7f29f4a7b29e4a772
|8,0=>0xba86e91ba06e71b986e51b906e31b886e11
|9,0=>0x2eb0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 14 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|4,0=>0x1000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000010000000000000000000100001000000000000
|5,0=>0x20000000002000000000008100040030000000080000000000100000000010000000000000020810000000000001000008000000000000000001000090800000003000000000000003000000000000000000010c0000001000000000000000000104000000400100041001000000000041000008000000000000000000000000000000000040003000000000000001000000000100000000000000000000000000400200000000010000001000000000000000041000000000000000000010a001000008000000200000000200000001000000400000000000000800100000000010000000000001000000088042000000000000000000000000000000000000000000000040000400080000000000000000000000000000000001040000000000000000000000000000041000400104000020010000000000000000000000
|5,1=>0x300000000000000000
|6,0=>0x10000008040a20010c9404b043030410400104000010004000040081044030b0000004000040000400000000000440014030004009801000500200400072000500100002400410b001400200200200002008020c000040000400000402080432f000002004004004008800012700104041030406b0000010329000080000400001140010000000140000080000400008000080800400008100230000c00100000001024500088000080010004000000081059908008000900018f000002000b00000002000024f00044000280010800008000080000004004401c21000400004001000098800004401c200000000000010000300040280000000008000040400002088103964018a000a0003000004400100000080014f00000000000410800204040090000020001010041040000000040003000540005001004004802082
|6,1=>0x410f90121840010010b00100000001020d000000000800008000080000400040400ca01080000000090c00104
|7,0=>0x404c1014f04149401434014300340003004010f00383c0048041270416f8012b041070430b0508a0014f040670016f0098a1010f1014f1404714047001644024f0406f00143c004f340470422740147040271418f0404f041670010c0016784007c0303840004024b4010f840070406d001ca041674014080107040a7401cf40104c020c
|8,0=>0x41634014f0012b04163003070010f0014f0416f041671400f
|9,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 20 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_233,8,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 1 then [(dom_171,8,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 2 then [(dom_234,7,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 3 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 4 then [(dom_169,7,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 5 then [(dom_227,6,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 6 then [(dom_107,6,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 7 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 8 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 9 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 10 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 11 then [(dom_225,5,runOps true dom_225 (0,roots_225) ops)] else [])++(if pm.testBit 12 then [(dom_201,5,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 13 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 14 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 15 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 16 then [(dom_139,5,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 17 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 18 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 19 then [(dom_75,4,runOps true dom_75 (0,roots_75) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_235 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_233 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) low_227 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) low_226 _ g hchk
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_225 _ g hchk
    · exact cpcs (by decide +kernel) low_201 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_195 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
    · exact cpcs (by decide +kernel) low_43 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_75 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_233 8 s (0, roots_233) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_235 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_233 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_235 == dom_235) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 1 zs symsG zs (hk 1 zs)
theorem ori_ok {v ys} (h : RunD true dom_235 goalM v ys) : RunD true dom_235 goalM v (ori ys) :=
  pickMin_runD 1 ys h symsG ys (hk 1 ys) symsG_ok h

def Z (s : Nat) := barP true dom_235 goalM mpG SD SS NN htAt idxH ori 1 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_12 : ∀ i, 12 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_24 : ∀ i, 24 ≤ i → i < 36 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 24 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 36 → Z 4 i = true := (range_split (range_split z4_0 z4_12) z4_24)
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
private theorem z5 : ∀ i, 0 ≤ i → i < 132 → Z 5 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z5_0 z5_12) z5_24) z5_36) z5_48) z5_60) z5_72) z5_84) z5_96) z5_108) z5_120)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_144 : ∀ i, 144 ≤ i → i < 147 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 144 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 147 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108) z6_120) z6_132) z6_144)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_12 : ∀ i, 12 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_24 : ∀ i, 24 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_36 : ∀ i, 36 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_48 : ∀ i, 48 ≤ i → i < 53 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 48 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 53 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_235 goalM mpG SD SS NN htAt idxH ori 1 pool6G mkCut s i = true := by
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
  scr true dom_235 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_235 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_235 roots_235 goal_235 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_235

theorem low_235 : Lower true dom_235 roots_235 goal_235 10 := S_235.noCircuit

theorem low_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (d:=dom_83) (dSub:=dom_82) (T:=goal_83) (TSub:=goal_82) (roots:=roots_83) (rootsSub:=roots_82)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_82

theorem low_83_l1 : Lower true dom_83 roots_83 goal_83_l1 5 :=
  lower_slice (d:=dom_83) (dSub:=dom_82) (T:=goal_83_l1) (TSub:=goal_82) (roots:=roots_83) (rootsSub:=roots_82)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a, 0, 1)] (by decide +kernel) (by decide +kernel) low_82

theorem lowZ_83_8_1 : Lower true dzo_83_8 roots_83 gzo_83_8_1 5 :=
  lower_iso (d1:=dom_83) (roots1:=roots_83) (T1:=goal_83_l1) [(dom_83, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_83_l1

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

namespace S_91
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,65), (2,18), (2,66), (3,11), (3,19), (3,67), (8,9), (10,11), (10,26), (10,74), (16,17), (16,18), (16,80), (24,25), (24,26), (24,88), (64,65), (64,66), (64,80), (72,73), (72,74), (72,88)]
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
|4,0=>0xbd48c
|5,0=>0x9e6e6
|6,0=>0x3f37a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xc0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0000f000f00000000000f000f00a0a0a0a000000000a0a0a0af0f0f0f0000000000000000f0f0000000000000f0f000030303030000000003030000
|_,_=>0
def stPool : Nat → Nat
|0=>0x46673346c688
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
|5,0=>0x17
|6,0=>0x3d
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_89,5,runOps true dom_89 (0,roots_89) ops)] else [])++(if pm.testBit 1 then [(dom_83,5,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 2 then [(dzo_83_8,5,runOps true dzo_83_8 (0,roots_83) ops)] else [])++(if pm.testBit 3 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])++(if pm.testBit 4 then [(dom_75,4,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 5 then [(dom_27,4,runOps true dom_27 (0,roots_27) ops)] else [])
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
    · exact cpcs (by decide +kernel) low_83 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_83_8_1 _ g hchk
    · exact cpcs (by decide +kernel) low_82 _ g hchk
    · exact cpcs (by decide +kernel) low_75 _ g hchk
    · exact cpcs (by decide +kernel) low_27 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_89 5 s (0, roots_89) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_89 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)]]
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

theorem low_211 : Lower true dom_211 roots_211 goal_211 6 :=
  lower_slice (d:=dom_211) (dSub:=dom_210) (T:=goal_211) (TSub:=goal_210) (roots:=roots_211) (rootsSub:=roots_210)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a00000000000a000a00000000000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_210

theorem low_211_l129 : Lower true dom_211 roots_211 goal_211_l129 6 :=
  lower_slice (d:=dom_211) (dSub:=dom_210) (T:=goal_211_l129) (TSub:=goal_210_l128) (roots:=roots_211) (rootsSub:=roots_210)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a00000000000a000a00000000000a000a, 0, 1)] (by decide +kernel) (by decide +kernel) low_210_l128

theorem lowZ_211_8_129 : Lower true dzo_211_8 roots_211 gzo_211_8_129 6 :=
  lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=goal_211_l129) [(dom_211, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_211_l129

namespace S_219
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,65), (1,129), (2,18), (2,66), (2,130), (3,11), (3,19), (3,67), (3,131), (8,9), (8,136), (10,11), (10,26), (10,74), (10,138), (16,17), (16,18), (16,80), (24,25), (24,26), (24,88), (24,152), (64,65), (64,66), (64,80), (64,192), (72,73), (72,74), (72,88), (72,200), (128,129), (128,130), (128,136), (128,192), (144,145), (144,146), (144,152), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
|7=>0x2
|8=>0x1
|_=>0
def HT : Nat → Nat → Nat
|7,0=>0x98d14264bb
|8,0=>0x6f0dd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0ca0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f0000000000000000000000000f0f0f0f00000000000000000000000000000000f000f000000000000000000000000000f000f00
|_,_=>0
def stPool : Nat → Nat
|0=>0x2999ab1a3ec688
|_=>0
def stOffB : Nat → Nat → Nat
|7,0=>0x6606
|8,0=>0xc6
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 8 then fld (dictB (i / 512) (i / 32 % 16)) 220 (i % 32) else 0
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
|0=>0x393a
|_=>0
def opOffB : Nat → Nat → Nat
|7,0=>0x441
|8,0=>0x20
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 8 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 7), wireSAt ((code >>> 5) &&& 7)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 6 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|7,0=>0x7ff
|8,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_218,7,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 1 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 2 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 3 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 4 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 5 then [(dzo_211_8,6,runOps true dzo_211_8 (0,roots_211) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_219 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_218 _ g hchk
    · exact cpcs (by decide +kernel) low_217 _ g hchk
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) low_91 _ g hchk
    · exact cpcs (by decide +kernel) low_211 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_211_8_129 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_218 7 s (0, roots_218) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_218 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_219 == dom_219) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_219 goalM v ys) : RunD true dom_219 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_219 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_219 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_219 roots_219 goal_219 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_219

theorem low_219 : Lower true dom_219 roots_219 goal_219 9 := S_219.noCircuit

theorem low_187 : Lower true dom_187 roots_187 goal_187 9 :=
  lower_slice (d:=dom_187) (dSub:=dom_185) (T:=goal_187) (TSub:=goal_185) (roots:=roots_187) (rootsSub:=roots_185)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) low_185

theorem low_123 : Lower true dom_123 roots_123 goal_123 9 :=
  lower_slice (d:=dom_123) (dSub:=dom_121) (T:=goal_123) (TSub:=goal_121) (roots:=roots_123) (rootsSub:=roots_121)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) low_121

theorem low_243 : Lower true dom_243 roots_243 goal_243 8 :=
  lower_slice (d:=dom_243) (dSub:=dom_242) (T:=goal_243) (TSub:=goal_242) (roots:=roots_243) (rootsSub:=roots_242)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_242

theorem low_243_l161 : Lower true dom_243 roots_243 goal_243_l161 7 :=
  lower_slice (d:=dom_243) (dSub:=dom_242) (T:=goal_243_l161) (TSub:=goal_242_l160) (roots:=roots_243) (rootsSub:=roots_242)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a, 0, 1)] (by decide +kernel) (by decide +kernel) low_242_l160

theorem lowZ_243_8_161 : Lower true dzo_243_8 roots_243 gzo_243_8_161 7 :=
  lower_iso (d1:=dom_243) (roots1:=roots_243) (T1:=goal_243_l161) [(dom_243, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_243_l161

theorem low_235_l67 : Lower true dom_235 roots_235 goal_235_l67 7 :=
  lower_slice (d:=dom_235) (dSub:=dom_234) (T:=goal_235_l67) (TSub:=goal_234_l66) (roots:=roots_235) (rootsSub:=roots_234)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a, 0, 1)] (by decide +kernel) (by decide +kernel) low_234_l66

theorem lowZ_235_16_67 : Lower true dzo_235_16 roots_235 gzo_235_16_67 7 :=
  lower_iso (d1:=dom_235) (roots1:=roots_235) (T1:=goal_235_l67) [(dom_235, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_235_l67

theorem low_179 : Lower true dom_179 roots_179 goal_179 6 :=
  lower_slice (d:=dom_179) (dSub:=dom_178) (T:=goal_179) (TSub:=goal_178) (roots:=roots_179) (rootsSub:=roots_178)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a0000000000000000000a000a000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_178

theorem low_115 : Lower true dom_115 roots_115 goal_115 6 :=
  lower_slice (d:=dom_115) (dSub:=dom_114) (T:=goal_115) (TSub:=goal_114) (roots:=roots_115) (rootsSub:=roots_114)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a000a000a000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) low_114

theorem low_155 : Lower true dom_155 roots_155 goal_155 6 :=
  lower_slice (d:=dom_155) (dSub:=dom_153) (T:=goal_155) (TSub:=goal_153) (roots:=roots_155) (rootsSub:=roots_153)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0000000000000000000000000c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) low_153

theorem low_59 : Lower true dom_59 roots_59 goal_59 6 :=
  lower_slice (d:=dom_59) (dSub:=dom_57) (T:=goal_59) (TSub:=goal_57) (roots:=roots_59) (rootsSub:=roots_57)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) low_57

namespace S_251
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (1,65), (1,129), (2,18), (2,34), (2,66), (2,130), (3,11), (3,19), (3,35), (3,67), (3,131), (8,9), (8,40), (8,136), (10,11), (10,26), (10,42), (10,74), (10,138), (16,17), (16,18), (16,80), (24,25), (24,26), (24,56), (24,88), (24,152), (32,33), (32,34), (32,40), (32,160), (48,49), (48,50), (48,56), (48,112), (48,176), (64,65), (64,66), (64,80), (64,192), (72,73), (72,74), (72,88), (72,104), (72,200), (96,97), (96,98), (96,104), (96,112), (96,224), (128,129), (128,130), (128,136), (128,160), (128,192), (144,145), (144,146), (144,152), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
|5=>0x7
|6=>0x7e
|7=>0x127
|8=>0xcc
|9=>0x40
|10=>0xa
|11=>0x1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0xdfd7cc6034a89fc57c31458b137e2c35625
|6,0=>0xfe14afcff8f9812f8f68f4144efb27ef895eee09ed526ecf82e6f51e5a66e4b88e47d9e4421df805df765deee3dbb9adb366d9d9dd6829d5f1cd426fd2193d0976d0460cfcfbcb803c5500bf849be099bc9c8bc7f9bc62fba28ab7adfb19c7b0d3fb09a0b077cb02e9adc7aa9082a48b0a40eaa3fa2a3e299fe6e9e1119b4da9a7599a41e96edf9657395fd19439593d5b933db932e29123b8f2488910d8235e8168e801107fa817ea2a7acd278d467897b745aa72ad0714026e1a46dcb06a2026955767b4763e396021a5f2815e8415ba055b7e359a9d566d655a845313a523b650a084a87c42d11402593d1c33d1363acad3aafc3189c31844308423018d2f6fe2c6632bd4a281a72621e25b5125ae8215101f7571ef2a1b84e1880816307156d9156d00ea8b0b06208f4106ae80651801e6101e11015e900a1c
|7,0=>0x6c61f6bf836bf6a6bf2569331684406713d660fe64dde64a826446a63f8463dba61ffb6131360ce8601195c6225bf435b5345ad075a6f25912958b2c5762b55fc155ba454ed6546a452c7c523b6520e451f2b51e04518e1514b65119e4ea904d2084bfd44bb8e4a04e48f0748c8e467a044d8144d1e4468f4463b445e140de2405b1401b13fa6f3f19e3e28a3df3b3d3c63ca533c0b93bfd73bd58394dd394503942838dd53579f33eff33bc632c9831e1f31ccd30b742f4de2ea392c91a2bbc42b9042b72f2b6722abe62aa2028d5f27d3127c0c2500b24e8824bb7246a823b3d223f021bc12190b21380206751ff721f7bd1ec631dd401db6f1b5421ae531acc01a8df1a33e19f5517e901797715936126061076f106b91004c0f4dd0f1d70e1080d9a90cee80c7530a05f09aa106a4f05da2057de02a91015ff012dd001fd
|7,1=>0xd6536d61fbd5f01d5d0ed54e4d3f3fd323cd3170d1daed0f1ed02a8d0172cfcfbcf1b8ceae1ce62fce01bcd018ca57ac9cc6c9709c8718c84ecc7ec4c7328c669bc59eec4eeac46a4c4535c3518c32f9c2150be9fabe436be13bbdc5cbcff1bcb5dbcac4bc634bbeedbb85ebafebbac99bab21ba8a2ba15db8f46b5c1bb4758b465eb40f5b2804b0cc8b0387ae6a7acb75ac413ab7c9a97efa5fdfa5f3aa5180a0b179fb2f9f26d9e49a9e3139de989d1919c10d9bff79b05e9a61e985ec977e2977069647895fd195f78958b19587a945aa93bb99369c92492905828fd5c8fd538c0248bf768af7489d268976d88f538683286659865f28623f861528539e849b08402e832c082b0f815b380d6f80a1e7e1937df4c7b51b7a63d7a5d77a2db79edb79ddb797097925278f1377b6376b9976a8a7634974e0a73d2a72f8a6e7a8
|7,2=>0xffc64ff4e2fd7acf8fa4f86def812cf720cf604df5f70f4c40f4623f43b0f0eedf0cd2f07eaed7a4ecb1cec77dec0c6eae6fea909e9a57e86dee7316e7269e6e32e6af8e6a56e583ce1889e0a95dfd7fddfc1daa9eda621d98ded9579d72b7d70ae
|8,0=>0xa75dfa2e8ea2c28a0dd49c5049af169a62f99be098b929759f90c368f9018f0948ea598e1938dbe18c6f68c3ce8c0db8bf768ba698adbc889b9867878423382393803be800e17fb327f4157d62c7d2fb7cbbf7c38e79edb781fb753c774f9a731126ea756861667a906507964a576459663dba6353661f47604855fdfb5e83e5e6d55e1cd5dd255d4ef5d15d5b2fa5a1595994c55ba4532065257951bbf51338502ae4c4964b2ba49d0f48cc6473714675645501440fc435ae41e7e41b7f401b13ead73aee6381f336556359b333240329402ff652f0db2da152caaf2ae7f2a7b82a7812940f25808244bb23ec620d791fc391f2221efea1de5a1d6531c7711be9d1b5ef1b0151ae5319e3819a881627015d7e0f19e0efbe0e39a0de1a0be760bdfe0a8be09df80790805da7050b1048d20330901a380159e015260048100184
|8,1=>0xff6d6fed03fd7e6fd347fa213f78c8f76f3f6dc8f6a76f44b3f33f1f2f54f2e6ef19f8f0d36f043bf036bf01a7f0161ee5e1ec532eb69fea791ea159e8bbfe5f38e4479e3630e335de30a4e1deee0fc0e0a95df70cdc55ada0f0d9c0fd7faed71eed5fa1d5842d5552d4c00d1daed03fccef84c9705c874dc7e01c6d51c5f61c55cbc5466c5451c23cfbfe0bbfb16bebd2bcac4b99a4b977eb96bdb79fdb6869b5ea5b5993b40f5b3c81b3940b1c7cb0c2fb0394aff82aad19a92e3a82a8
|9,0=>0xfbeacfb518f37daf0201e5ea1e51b5e3d36e01c1dad38d749ad3cf6c9e19c8147c4495c4125be170b6de1b603db4540b1bf5b198db10a4abd25a621ca04b79a387945dd8e6598c0db8583f824cf8218e8028e7ff7b7dac67d24478e127584d740516cca36ba5664011602de5f1ba5d1bb5cc665ba1655ea152579518cc4afb4466e43a7f5366bb2f5362c573184dc1814717e4811ac60b8ab073ad055e702106
|10,0=>0xc20289a4ee8e0237849d6db67612cb353be1e33e15d4313b90
|11,0=>0xcdebd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f0f000f000f0f0f0f0f000f000f0f00000f0000000f0f00000f000000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f00000f00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00c0c0c0c0c0c0c0c0f0c0f0c0c0c0c0c0c0c0c0c0c0c0c0c0f0c0f0c0c0c0f0c00000000000000000000000000000000f0f0f000f0f0f000f0f0f000f0f0f00000000000000000000000000f0f0f0f0000000000000000000000000f0f0f00f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f00f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000f0000000000000000000000000000000000f0f00000f0f0f0f0f0f00000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f000000000000000000000000f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0000000000000000000030303030303030300000303000003030303030303030000000000000000000000f000f000f000f0000000000000000000f0f00000f0f000000000000000000000000000000000000f000f0f0f0f0f000f000f0f000f0000f000f000f000f000f000f000f000f000f0f00000f0f00000f0f00000f0f000000000000000000f0f0f0f0f0f0f0f0000000000000000000f000f0f000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000f000f000f000f000f000f00000000000f000f000f000f000f000f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000f000f0f0f0f0f000f000f0f000f00000f000f0f0f0f0f000f000f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000
|0,1=>0xf0c0f0c0c0c0c0c0f0c0f0c0c0c0c0c0f0c0f0c0c0c0c0c0f0c0f0c0c0c0f0c0000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f000f0f0f000000000000000000f0f0f0f0f0f0f0f000000000000000000000f0f00000f000000000000000000f0f0f0f000f000f00000000000000000f0f0000000f0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000f000f000f000f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f000f0000000f00000000000000000000000000f000f000000000000000000000000000f000f00f0f0f0f000000000f0f0f0f0f000f000f0f0f0f000000000f0f0f0f0f000f00f0f0f0f000000000f0f0f0f000f000f0f0f0f0f000000000f0f0f0f000f00003030303030303030303030303030303030303030303030303030303030300000000000000000000000000000000000030303030303030303030303030300000000000000f000f00000000000f000f00000000000f0f0000000000000f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f00000000f000f000f000f000f000f000f000f000f0000000f0000000f0000000f000000f000f000f000f000f000f00000000000f0f0f000f0f0f000f0f0f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f000000000f000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f00000000000000000000000000000000000000000000000000f0f0f0f0f0f0f00f000f000f000f000f000f000f000f000f0000000f0000000f0000000f00000000000000f000f00000000000f0f0f0f000000000f000f00000000000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f00000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000000000000000f0000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f000f0000000000000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f00000f0f00000f0f000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f000f0f00000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f00000f000f000f000000f0f0f0f0f0f0f0f0f000f000f000f000f0f00000f0f00000f0000000f000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f00
|0,2=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f0000000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f00000f0f00000f0f00000f000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f000f000000000000000f00f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000f0f00000f00f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0000000000f000f000f0f0f0f0f0f0f0f000000000f000f000f0f00000f0f0f00f000f000f000f000f000f000f0f0f0f0f0000000f0000000f0000000f0f000000000000000000000000000000000000f0f0f0f0f0f00000f0f0f0f0f0f0f0000000000000000000000000000000000f0f0f000f0f0f000f0f0f000f000f000000000000f000f00000000000f000f00000000000f000000000000000f0000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f0f0000000000000000f000f00000000000f000f00000000000f000f0000000f000f000f0000000f00000000000000000000000000000000000000f0000000f0000000f0000000f00000000000000000000000000000000000000000000000000f0f0f000f0f0f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f0f000f000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f00000f00f000f000f000f000f000f000f000f000f000f000f0000000f000f000f000000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f000f0f0f000f0f0f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f0000000f0f0f0f0f000000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000000f000f000f000f000f000f000f0f0f0f0f000f000f000f000f000f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f000f0000000f00f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00000f0f0f0f000f0000
|0,3=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f00000f0f0f0f0f00000000000000000000000000000000000000f0f0f0f000000000f0f0f0f0f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f000f0f0f000f0f0f000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f000000000f000f000f000f000f000f00000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f0000000000000000000000000000000000000000f0f00000f0f00000f0f00000000f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f0f00000f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f000f0f000f000000000000f000f00000000000f000f00000000000f00000f0f00000f0f00000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f0000000000000000000000000000000000f0f00000f0f00000f0f0f0f0f0f0f000000000000000000f000f000f0f0f0f00000000000000000f000f000f0f0f000000000000000000f0f0f0f000f000f00000000000000000f0f0f0f000f0000f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f0f000f0f0f0f000f0f00f0f0f0f0f0f0f0f0f000f00000000000f0f0f0f0f0f0f0f0f000f0000000f00f0f0f0f000000000f0f0f0f000f000f0f0f0000000000000f0f0000000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00000000000f000f0000000f00f000f000f000f000f000f00000000000f000f000f000f000f000f0000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f0000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f000000000f000f000f0f0f0f0f0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000f000f000f0000000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0000000f0000f000f00000000000f000f000f000f000f000f00000000000f000f000f0000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f000000000f0f000f0f0f000f0f0f000f00000000
|0,4=>0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000f000f00f000f000f000f0000000000000000000f000f000f000f0000000f0000000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f0000000f0000000f00f0f0f0f0f000f0000000000000000000f0f0f0f0f000f0000000f0f00000f000000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000f000f000000000000000000000000000f000f000000000000000f0000000000000000000000000000000000000000000000000000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f00000000000000000000000000000000000000000000000000f000f000f000f00f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f00f000f000f000f000f000f00000000000f000f0f0f000f0f0f000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0f00000000000000000000000000000000000000000000000000f0f0f0f0f000f0000000000000000000000000000000000f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000000000f000f000f000f000f0f0f0f0f0f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f0f000f00000000000000000000f000f000f000f0000000000000000000f000f000f0000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f00f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0000000f0000000f0000000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f000f000f000f0f0f00f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0000f000f000f000f000f000f000f000f000f000f000f0000000f000f000f000000000000000000000000000000000000f0f000f0f0f000f0f0f000f0f0f0000
|0,5=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f00f000f000f000f000f000f000f000f000f000f0f0f000f0f0f000f0f0f000f0000000000f000f00000000000f000f00000000000f000f00000000000f000000f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0000000000000000f000f000f000f00000000000f000f000f000f000f000f00000000000f000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f000f000f000f0000000000000000000000000000000000f0f0f0f0f0f0f000f0f0f0f0f0f0f00f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f000f0f0f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0000000f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000000000000000000000000f000f000f000f0000000000000000000f0000000f0000f0f0f0f000000000f000f00000000000f0f0f0f00000f0f0f000f0000000f00f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000f0000000f00f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f000000f000f000f000f00000000000f000f000f000f000f000f00000000000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f000f0f0f00f000f000f000f000f000f000f000f000f000f000f000f000f0000000f000000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000000f0f0f0f0f0f0f0f000f000f000f000f0f0f00000f0f0000000f0000000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f00000000000000000000000000000000000000f0f00000f0000000f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0000000f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f00000f0f0f0f000f0000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000000000000000000f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0000f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f000f000f000f00f0f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f0000000f0000000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f00f0f0f0f0f0f0f0f00000000000f000f0f0f00000f0f000000000000000f0000
|0,6=>0xf0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f000f000f0000f0f0f0f0f000f000f0f0f0f000000000f0f0f0f0f000f000f0f0f0f00000f00000000000000000000000000f000f0000000f0000000f0000000f000f000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0f00f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f0000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f000f000000000000000000f000f000f000f0000000000000000000f000f000f000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000f000f0f0f0f00000f00f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f00000f0f00000f0f0000000f0000f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f00000f00000000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f00f000f000f000f0000000000000000000f000f000f000f000000000000000f0000000000f0f0f0f00000000000f000f000000000f0f000000000000000f0000f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f00000000000000000000000000000000000000000000f0f00000f0f00000f0f00000f00f000f000f000f000f000f000f000f000f0000000f0000000f0000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f00000f0f0f0f0f0f00000f00f000f00000000000f000f000f000f000f000f00000000000f000f000f00000000000000f0f0f0f0f000f000f0f0f0f000000000f0f00000f000f000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f000f000000000000000000f000f000000000000000000000000000f000f0000000f00f0f0f0f000f000f0f0f0f0f000f000f0f0f0000000f00000f0f0000000f00000000000000f000f00000000000f000f00000000000f000f00000000000f0000f000f00000000000f000f00000000000f000f00000000000f000f0000000f00000000000000000000000000f0f0f0f0000000000000000000000000f000f00f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f000f00f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0000000f000f000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f00f000f000f000f000f000f00000000000f000f000f000f000f000f0000000f00f0f0f0f0f0f0f0f00000000000f000f0f0f0f0f0f0f0f0f00000000000f0000
|0,7=>0xf0f0f0f000000000f000f000000000000000000000000000000000000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f00000000000f000f000f000f000f000f00000000f000f000f000f000f000f000f000f000000000000000000000000000f000f000000000000f000f00000000000f000f00000000000f000f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f000f000f0f0f0f0f000f000000000000000000f0f0f0f0f0f0f0f00000000000000000f000f000f000f00f000f000f000f000f000f000f000f000f000f000f000f000000000000000000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f000f000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f00000000f000f000f000f000f000f000f000f000f0f0f0f0f0f0f0f0f0f0f0f0f000f0000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f00000000000000000000000000000000000000000000f000f00000000000f000f0000000000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f0000f000f000f000f000f000f000f000f000f000f000f000f000000000000000000000000000000000000000000000000f000f000f000f000f000f000f000f00f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f000f0000f000f000f000f000f000f0f0f0f0f000f0000000f0000000f00000f0f0000f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0000000f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f000f000f0000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0000000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0f000f0f0f0000f0f0f0f0f0f0f0f000f000f000f000f0f0f0f0f0f0f0f0f000f0000000f000000000000f0f0f0f00000000000f000f000000000f0f0f0f00000000000f0000000000000000000000000000000000000000f0f00000f0f00000f0000000f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000
|0,8=>0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f000f00000000000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f000f000f000f000f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000f000f00
|_,_=>0
def stPool : Nat → Nat
|0=>0x28200009110180803010844004018180a000e80818040181c101c0d80c10000301c0a1a0200c2e000c8181204018000a060c00808030b80004060b0100600030140e150200c0e0503000280c0200c0e080083c08030500816000200c0005038182605018200c12088300803010041e060200c1c100101006070083c0004018380c09010300803040041a04018080200
|1=>0x1c8100600010240a370200c0a02000186c050181c0c001a8d00e04018200c0e198100600028180e320200c0a31118240404018000a06010c00803000080c05178100600028b812020200c0c050001c5a04018b04006048080803000140c2b0101006060281c002a0200c0006038145204018000c05038a00a04018001226010140803118940404018141202000900803
|2=>0x10149004018180a00039280803030140e002481006170400012480200c0c00010148e050200c0009228080803000140c430101006060001484020200c0006038148204018000a40048080803028204223048100600048080a1b018200007030147e060200c0002028f808030301400071e810060602808003c0200c0c050001c7604018181200028e80803038140006
|3=>0x18180a020017008030001c0c052d810060003014b4020200c00072c8182c04018180a002c00808030301400570101006080701c0c090200c0c05001580404018180405001540803038140c002a0100607030000a530200c0c050001ca2040185c0400031400803278c40c0901018080300014044d0200c0e01040000803030140007260100600030080a4b0200c0009
|4=>0x378080e04018200c0e37010060003014da020200c0a0203000d804018000e06029ac08030b8000c6906010066833824cc05018180009010d408030385c0006328100600048080a640200c000503024c604018000c02029880803000140c610101006000281804600200c0e0600014be04018180a000397808030001804052e81006000291012020200c2e00010183804
|5=>0x18000a063d8080c04019dc04053f8100605010000c7e0200c000503818fa04018180a003e00808030b82000063d8100600038180a7a060100617339e408030301400780101408030401824060200c1007071d418040181c10013a01006060281c00730200c1021100181204018180a00011c80803030140e00388100605010000c220200c0006029c00404018000a06
|6=>0x381514060200c00051f13418040181c0c08448100617010800c840200c0a02108184604018140400032200803030140002438100600030150c020200c0a0904000ac040185c0085030240803000140c092701808030401c1c1006010060604070e40c0200c1002008100617010000c830200c00050320804040185c0400032040c04018380e020200c0e06028010004
|7=>0x10000803040000a070324418040185cd0670483008030299c0e79028100607030012004018180a080001cf8060200c9e31038080803030140007012380803000181202029640803000180409028e00803028c40c23038080803030151a0003a300803000140c2e038080803030141000039e018040181c0c080e17418040181c0c1c3d0100617010000c480200c0006
|8=>0x1818108b028bc0803000180a810380808030285c04000308c08030385c10000320c1804018200e0602a540803040000a07032081804018200a06049c81804018200e93030701804019a0ce072e83008030302004052581006070b8200006408100606028000e8e0200c10000281c0c7b0200c1000038180a920281006060009c04040181c0a0800018fc04018141409
|9=>0x440100600038080a060d8100608000180e05430180803000140e0231810060002a140e06048100608038180a004f03008030382116053201408030381800094e83008030300812054e01006074c02000064181808030b808004f030100600038153404018000c054181c04050200c0c0012808080303014100003a64080303a601000032040803040000e0602a5c1804
|10=>0x401cb2060b01006070b82000062401406080381800350200c0e98040800c840301006000281cc604018000a31030240404018200e06028014a040181440064201c04040182000050301d480c0200c0e05518191604018000a062001c0404018200005510181204018180a070400140040181c2e08100190808060100607008100607028204206118100607028200006
|11=>0x280152050200c1006000253e060200c2e02000800a040180046090101006000300812052e83008030302004052e830080303a84d0670200c0006029200e02060100608338240a66060100617040080c1c0200c140705820000c0200c0e060405928060200c007701014b2040181c0a08000195004018180a0003a9c0803038141000032980803030140e87000300803
|12=>0x101808030382042200200c0e05040000cb403010060002acc0404018200006038156204018180a080001c3a060200c0e05002bc18040185c0c08348100600028640e060481006080001c0a06568300803040140e090d8300803048200405320100607028215806118100600038080c050b014080304018ec770200c0c050382000ab0200c1000028180e18038100606
|13=>0x4018120002ae008030b82000063501006060282000075b83008030399c12053d01006080001812053301408030401c00091301408030408c0e250200c0006048080a930200c0a17000080c8b0200c0a08000840c090200c0a070482000240601006071b99cd00c0200c0e06040152804018200e06000156c0c0200c0c090101546060200c0a02002d40c04018000a3e
|14=>0x200c0e0604058ba060200c0005038089c04018200a311181c120c0200c106803024cc04018200005038186004018200006038157604018000a062201c04040182000051701c120c0200c2e06040242c0c0200c10055d0191604018180a00038092a070200c0c05002e41804018180a08011c80803040b040070302418040181c0c080292c0803040000e05030ac0803
|15=>0x281c047a0200c1007030000abe0301006070b8010a060200c0005039380a040181c0c004e81006000381812053d0300803038180a083d01006080001c0c055e83008030501c10090e0100606028003e070101006080001c12051b8100606028780077010180803000080aba0200c0e05040000c360281006080300012b20200c0007010140c6406010060504821780c
|16=>0x3419c0e091c0300803040140c09620300803041a00e091b81006070282000066181006060281c10001e01808030001544020200c0c050382000c20200c1007030000ac1060100606040240a950200c0a170400046090200c0c0505000ee0206010061704019161c0200c0c05040000ec00200c0c05002a80e020200c0e050302000bf0200c0c05468000e77060100606
|17=>0x200c0c05040090e040181c0a08000199604018180a5d0100018040181c10090299018040181c100902b280803040000a40038240803040000c0702b2408030301400c80380818040185c10063c81006060282000076381006080001c0c05630180803001dc04054983008030302012051781006050b80800064203008030381810050e0140803030001246010300803
|18=>0x29c80803040000e09029200e04018000c053283008030302116053301808030385c00190200c0c050001c04940200c0e05040000ccd0200c0e05041fc0c840281006000327c0404018180a002901c0404018000e02030152c04018200007030159804018200e06000148e050200c1007000248a040182000050301c860c0200c0e67048153804018200e0600014840c
|19=>0x18180009138080803000180a50038080803038140c080034418040181c040602a700c04018000e055c0e8080303014cc020001006070b8200006280140803000184c020601006070419c0a5d03010060501000420c0200c2e08010182c04018209e3103818120c0200c0a0704025a004018180a07040019e04018200e06000159c0c0200c14080102c180401818108b
|20=>0x1cb004018000a2c03024040c0200cd06703824ba0c0200c0e0645814f404018180a080001daa0c0200c0e08458146e060200c00050393408030001804050581006060282000072b8180803160800e020200c0e050401800d3060100617040182c0c0200c0c0904014b20401820000603815a404018180a080001cac04018200e0602800aa060200c00055c0080a04
|21=>0x1488070481006060281cf4000200c0c0503820005c0200c00052781812020601006080281c12da0200c0a0200019a8040182000060281cb40401820000603815b20c0200c0e06042503804018000a066c01c04040185c1000278181204018200e0602801ae040182000050301dac0c0200c0e0604258380c0200c10072c818380c0200c0e06040707004018180a08
|22=>0x200c0e05043840c84060100608010180a2f0200c1007030000ae00200c1000038180a62038180803040380803040000a06039840803040000a070318008030001c0406028700c04018000e051d0100608000180a076f81006080001c0a066f0100606028011e070101006080381800056e81006080001c0c052e81006070282000066e01006080001c0a066d8100608
|23=>0x301cde040182000060281cda0401814140904000ee040185c10001001812040181c0a0803000d80c0200c0c0204814f40c0200c1002048146e0c0200c2e080339c0803038141000033980c040181c0a00728100600038180a690200c10070301400e40200c0007029640c8b060100608038140c1b0280c10070300012350200c10000281c0ce20601006070422c0a1b
|24=>0x458153804018200e0602801d6040181410005a8181204018200005030247c040182000055981812060200c0e0202800fe0c0200c2e080322c2c04018180a080001dd4060200c0005038f89c0c0200c0c0503809d20c0200c2e060402438050200c0077010191604018000a20030240404018180a001201c04040181c0a080001844040182000060281ce004018200005
|25=>0x200c0e050400158050200c10000301d64040182000052781c0c090200c0e05040000cd406010060603a8410680381808030413c620c0200c100703015d80c0200c0c09040080a930601006050b82004064583008030301ccc08340180803040000a077181c0803040146206118100608000145807030241804018200a0703025280c0200c120801014360c0200c0e06
|26=>0x18200e0202818c80c0200c0e061b820d0070200c10000301506050200c1007030008c0706010061e3419c180401818120802bb8100c0200c2e06350300803030140e084a830080303820d0066a01c0803040000c054082018040181812053301408030001846070103008030285c1006458300803030141007012541804018200a070302496040181c0a061b8200006
|27=>0x38240a370301006080001c0af10281006080001c0c450301006070282000e1038100608028800c840200c1000028800e060483008030401c0a06320300803038140c086501c0803040000a062003008030401c0c05738300803040180a07178300803038181205041e818040181c10670481470060601006080101574060200c0a17010001804018200a0603b101804
|28=>0x28200e024a03008030301410075e03008030401c040602a581804018200a070331418040181c0a08033d018040181c0c0802bc81804018200e050334008030301414080001d1804018200007030240a380601006060297410020601006050501c10094581c0803040000c0524030080303818108b0285818040181c0c08048143804018180a1e040000e8c040300803
|29=>0x29740c040181c2e080013c0a04018200c09001dc18040181c0aa30319c0a04018200e06000941804018281068038240c04018000a2c038080803038142e0800018460c0200c0c050401d280c0200c0e06040152c0606010060803814b20c0200c1068038181238028100600038080c8b0601006053419c0e090281006080381800270200c0a0a038241000060100606
|30=>0x1820000702a6c0e04018180a080007c1804018180a0803be80803040000a3103818120c0200c0c080101416050200c100703000ec070200c100002818880c0200c0a1704019d0060200c00052781c040c0200c10050301c960c0200c100503819b4040181c0a98040000c23060100607030240a084e030080303014cc080103008030401c0a067b030080303820ce09
|31=>0x29640c8b0601006070302116051c018080303a6010001001808030001440070101408030001908070101408030001812020301006070b8200020060100608038080c050e0300803043b40e06049740c0401820000702ab80e060200c00054281c08030301410005501408030400046070481006080001c0c09029741804018180a07041e81804018141002033500c04
|32=>0x2c83008030381810057d830080304015de070481c08030301410002901818040185c10f70200c1000038180a380601006070301410690381006060282000c80601006070302116054a01808030381410005a8180803040000a071f0180803040000a0759830080303818108b02a58180401820d00703024ba0806010060703014ba0c0200c0e0604014380c0200c1007
|33=>0x181c0a08033fc1804018140e5d0419c1804018180a08038091c04018180a1e040000e770601006080281c0cfe0601006060482004052c8300803030141007390300803030200409028e01804018200a07033f018040181c0c08048142c0c0200c0a1704820ce0c0200c106803818700401820000703014d407030100600028640e04018180a8d0001808030001c0405
|34=>0x300012460200c0a17040000c090601006070302116052e830080303818108b028700e04018200005033600c0401820000503a8808030301414080001cee0c0200c0c050401d1c0c0200c0a1703021e60c0200c0a082c8181207030100608160801804018142e0604025160c0200c0a0a0482004060281006003b8080e040182000060294018040181c0c05042701804
|35=>0x601006070419c0a0b028100608000180e9f06010060503a8410670200c0c050f0000e0206010060802ae80c09060100617041a00c090601006080281c0c790601006060397410ed060100608038080a060d81006060281cba0800010060702a601000032100e04018180a080023c18040185c10ed030240c04018000a31038080803038142e080001908050200c1007
|36=>0x181c0a370419c0c040181c0a08000840e04018180a080009018040181d30680319c180401818100204814ba0606010060701015460c0200c0e0904015e00c0200c0c050401d4e04018180a0a0001c040c0200c0c050401d0e0c0200c0a087a818120c0200c0e1734018ce0c0200c106803818ba0c0200c0e0503022000c0200c0e0504018360c0200c100702a4c0c8b
|37=>0x40240a96038100608000140c2e0200c1000038180a0b0200c0c0503a8410000403008030501c16060200c10000381570050200c10070300012270601006070301411010301006070282000b003010060702820007f060100608038080c050b01006060281ccc08000300803040140e0604b140a04018200007030981804018180a07043a40c04018000e0202a4c1804
|38=>0x303008030401c04052c81c1804018200a067c82018040181c0c09029740e0c0200c1005033bc18050200c0c09040080e0c0200c0c05043f41804018200a68038181206028100600038080e050200c10000308c1804018200aed03818120c0281006070302116080601006050501c12060601006080281df00c0200c0a088101c120c0200c0e06040142c0c0200c0e06
|39=>0x200c0e050b8200c670303008030381410f5030140803040000e8c03030080303a601068030300803040140eba0303008030385c106803010060702a601000038180803040000a4f0303008030385c10ed040300803038180a6a0601408030401c0ce80301006070285c1000038180803040000a2c030300803038141059040300803038180a3803830080303014108d
|40=>0x3a8418050200c0e0604025160606010060803815dc080601006060281ccc0606010060803815260c02810060704820ce06060100608038080a93038300803030141102060100606028281007010201804018180a072e83008030381530080319c0e060200c1000028801804018180a1e0401c04080601006050b818120702810060800019080706010060803015e00c
|41=>0x41a00c0c0200c0e050428c0e0c0200c0a680319c0e0c0200c0c1e041a00e04018180a0a040000c0c0200c100702bdc0e0c0200c0c1e043b40e04018180a1e040000c0c0200c0a1704008100c0200c0e05030dc0e060200c1000028c4100c0200c0e05033500a040182000070302418050200c0e06043cc0e0c0200c0a1e0419c100c0200c0e060282c100c0200c0c05
|42=>0x1007030300a040181818050200c1007010200e0c0200c0c05050200e0c0200c0c050f02018050200c0e060481c0c0c0200c10053401c0c0c0200c10057681c18050200c1006338200c0c0200c0e054c0200c0c0200c0e050b81c0c050200c10000403008030381812051c0300a04018200e020322c0c050200c1000039dc0e0c0200c0c0a
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x8d803ac0176008b002d800ac0005
|6,0=>0xef3875dc3a0e1c970e1386edc368e1ad70d33867dc330e19260c5b8611c2fae17670b7b85a1c2c2e15a70a9b8531c28ae13e709bb84c1c252e122708db8451c21ae106707fb83e1c1e2e0ea7071b8371c1aae0ce7063b8301c172e0b27055b8291c13ae0967047b82258104e07b703ab01b9c0cee060702cb8149c096e044701eb80d9c060c0297
|6,1=>0x716e38471beb8dd9c6dee36871b0b8d69c6a6e34c71a2b8cf9c66ee3307194b8c8d8638e315718738c218602e2fa7179b8bb1c5cae2de716bb8b41c594c2c3715eb0ad9c55ee2a87150b8a69c526e28c7142b89f9c4eee2707134b8989c4b8c25571273891dc480e2397119388adc448e21d710b3883dc410e20170fd387cdc3d8e1e57
|7,0=>0x2bdc15ce0ad8e56482aeb95560a9b0545829ec14d60a5b0525828ec14560a1ec507827fc13de09df04e7826fc135e099f04c7825fc12de0960e4a97250c1269c925048a8241411ea08e5046a82314116a08a5044a8221410edc867042b8212390720829040d7202c0ff9c7ed03ef71f438f85c7b303d271e540f0a077503b281d540e8a073503928
|7,1=>0x3b4c1d860eb3075183a4c1d060e7307318394c1c89ce350712838541c0a0df506f37375c1b8e0db706d3836639b120d7906b4835641a95cd3b06958346c1a19ccfee6787338419a5ccc3065983293992dcc87063b8319c18ae0c47061b830a398320c0905fd72fac17b9cbcee5df82ebc1741cb9105c082dc416c5cb5305a182ccc1649cb1505837
|7,2=>0x4b03a56212a1094884a0ba4e6126309298490c2466122309098480c23e611e308ea74714236a11a508ca8461422edd16708ab8451c226e1127088b8441c21ee10e7086b8431c216e10a8e84c8422420f21069082c8412420721029080c840241ff20fe907ed73f339f7dcfaf07cf83e3c1efe0f6f07af83d3c1e81cf31079083c441e05cef307718
|7,3=>0x5a942d2a16850b3b7599c2cae16470b1b8589c2c2e16070afb857a3abb215c90adc856abab36158b0abd855ac2ab6154b0a9d854ac2a36150b0a7d853ac29b614cb0a5d852ac2939d48eea3f851c3a8c21452ea21850cc284614130a0274fd427ca13d509e284ed4274dd39709c474de426d5d35b09a584cec2656131b098674bf425da12dee9678
|7,4=>0x321618fb0c758636c319618bb0c558626c3116187b0c358616c3096183b0c158606c301617fb0bf585f6c2f9617bb0bd585e6c2f19d77d0bb775d83aea217410b9885c842e2217010b7885b842da216c10b5a6
|8,0=>0x74a43a321d090e7b9739c39aa5cc50e5a87294392a1c832e3897184389e5c3f0e169706cb8125bf90df486f6437921bb90dd396e5c370e1b770db386d5c368a5b332d9186c53b60a1af32d7186b4c35861ab4ed5286a5bb50e1a770d338695c348e1a370d129684cb40619f30cf186744b38219b10cd17664c3302596f2caf8653c327e192d2c8d9
|8,1=>0x84ec4256211cf087783fc41de20df106788303c16220a11048881fcc0de205f1027880f4c056601b100587fe4bfce5fd70fe387edc3f51df990fc397dd4beca1f56efa387cdc3e4a5f150f8287bd43dca1ed50f6197acc3d461e930f41879cc3cc61e530f20978bcbc3e1e0f0efe977b43bba1dcd0ede876b43b3a1d8b2ebd875ac3ab61d492e9c8
|8,2=>0x955cca8e25353292894544a0a24f5127289354498a24b332518924c4906247312318914c4886243312118904c480263f111f088f44478223b111d088e444702236f31af88d34c67a232d118e88c2cc5f262e9116b98b14c56a22a5114998a0c44e62263112a7890cc4662224f10a8881443ea21e510e998704c362219f30c7885f4c2da215b30a58
|8,3=>0x986c4c1625f932f4897644b9225baf2d589664cb12257912b48
|9,0=>0xa8bcd43a6a0d14fe8a7b453ba29cd14de8a6b4533a298d14be8a5b452ba294d149e8a4b4523a290d147e8a3acd1b628cb145d8a2ac51326889143b9a19c50aa684514199a08c5026280313f899f844fa227c113d889e844f22278113b889d844ea22741139889c844e222701137799b7c4d9a66bd135689a744d16667cf3368996ccc96263b13158
|10,0=>0x2acf155f8aabc553e2a8f153f8a9bc54be2a4f15207
|11,0=>0x156f7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 259 then fld (dictB (i / 512) (i / 32 % 16)) 252 (i % 32) else 0
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
|0=>0x403103815030e1048160401d03819040310303a100b30001500014040310401d0309d0002703819040310401d0002403819000190403100029040310401d03819030161185c03819000190403103815000150005c040310401d038150401d0387d000780403103015040060582904817038190301604031048170401d03819030160403104006058290481703819030160403105829048170401d0381903016
|1=>0x40150493f0401d038190001604031048e1048160401d03819040310401d03819030b1000140403103819100b30001500014040310114b0401d0007b040310301503939010820401d00015040310403105829048170381903016118140401d03819000190403111814038190001904031038150401d2301b0002503819040310401d03911030b100014040310401d03819030c5000170403103819000190005c
|2=>0x5829048170401d038190301602a110001b040310401d038150401d100b30001500014040310401d10024038190001504031100240381900015040310381534024038190401904015038153b9d90001f00026038190403103839100b300015000140403104005058290481703819030161185c00019040310401d0381503039100b3000150001404031041a904814038190403103815038e1048160381904019
|3=>0x2603819040314781f0007904031030150401d000170001604031010150401d0381904031048160401d03819040310401d0001900017040310001d040310407a030150401d1001b00015040311201f000290403103016048154581704025038191181400019040310401d038150001b00015040310401d03815000190005c040310401d03815051dd0001f0403103819030160383a100b3000150001404031
|4=>0x11817000190403100019040310401d0381502a110001b0403103815030f91001f00015040314a01f3402503819040150481503819040190401504a4d010160401d03819118170001904031038150107a0401d0403103015100240381900015040310401d000270381904031108190005c0403103815040310401d0381903016048c70381900017040310381904019040150381534024038190401904015041d9
|5=>0x1904031038152c81b010150401d0403102a7d1181f00019040310113d0401d0001604031038190413d0001604031000e10481603819040310325945816040250381923023000250381904031040e1048160401d0381900016040310401d038150426d029df0001f040310401d02a110001b040310401d0002403819040310f1df0001f040310301513016031dd0001f0403103a594581604025038190401d
|6=>0x3a350407a030154581401019010150401d11814000190403103815230130002503819040314281d0413d00016040310401d038190001704031001a90481403819040310401d0001b0001504031038b91001b0001504031010190424d010160401d0401d030c5000170403103819038b1000140403100287040310387a030150001b00015040310381505829048170381903016000190005c04031038151185f
|7=>0x10190401d040310001f000260381904031042a90007a04031030152301f00025038190403100015040310401d038150401d038190001904031048150401d0381904031048e1048160401d0381904019040150387a030150401d118140001904031038e104816040190381945817010190401d0381504031048170381903016010150401d0001f04031010780401d04031030150ba110001b040310381504031
|8=>0x40310381903016040150401903261038160424d010160401d038190005f040310401d038150401d1001f0001504031000150005c04031038150ba130001b04031038150401d0393d00016040315901703a110001b040310387d000780403103015580230005d0403103815041a904814038190381503819100230001504031032b9460140001d040314a01b3402503819040150324d010160401d0381945814
|9=>0x1001b0001504031458140402503819038150101903a4d010160401d010290401d0403103016478230007904031030154a01f010790401d0301503819000150001404031029dd0001f03819040310481403819040310381504176048150401903819038e10481603819040310309d00027038190403100024038190001904031010160401d038190403101019040310401d03815038190005c040310381500029
|10=>0x160403103815040fa1001f00015040312302300025038190403104176048150381904031458170402503819030160401d000780403103015030e10481603819040310401d0001f040310301503a4d010160401d040310389d0002703819040310324d010160401d040310102b0401d03819030160481545814040250381903819000190001704031038e10481603819040150401d030b1000140403103819
|11=>0x40310401d038150401d0002503819040310481603819040190401503b15340270381904015030e10481603819040150401d038b100014040310289f000270381904031010e1048160401d03819038190001904031038150401d0001f040310301645817010190401d03815039490007b04031030150401d0007a0403103015000dd0403103261038160001f040310407a030154a023010790401d030150413d
|12=>0x2403819040312301b00025038190403103911030b10001404031040e104816040190381903a390107a0401d03015040310401d038790301503259458160402503819338e104816040190381903819030c500017040315901603a110001b040310401d0002b0403103016340240381904015038154607b0001d0403103015029174601b0001d04031010160401d0001f0403103a594581604025038190001b
|13=>0x31dd0001f04031048e10481604019038190005c040310401d0381545814010190401d03815038190001700016040314582b040250381903016048170401d03819030164a01f458150402503819118140381900019040310414102a130001b04031038e104816040250381910023000150403103815010790401d04031030150401d1181f00019040310401d0007b040310301513014031dd0001f0403112815
|14=>0x100230001504031048170401d03819040310f1dd0001f04031030150401d000150001404031003510b81b040310381545814010190401d038150124d010160401d0381902a7f1181f0001904031051dd0001f04031030160401d029dd0001f040310401d0002703819040310401d02a130001b04031000df0403103261038160425945816010190401d042e2029dd0001f04031040310401d03829030160401d
|15=>0x41760387903015001740403103879030150401d038190001604031033153402703819040150b81b040310401d0381502a7c1181f0001904031458174581504025038190401d0313d0001604031038190001604031038154581701019010150401d03aa90007a04031030150401d038190001404031048150381904019040154a023458150402503819460780001d0403103015030e104816040250381903865
|16=>0x48160401d0381902ba30101b0401d03815043850005e0403103815041a904814038190403101019010150401d04031230130002503819040317181b038c500017040314a01b45815040250381903a5945816010190401d100b30001500014040310493f03819000160403145817010190401d04031042e2029dd0001f040310401d000790403103015048e104816038190403103819030b1000140403104031
|17=>0x5f04031038151001f038190001504031038190393d00016040310024d010160401d04031040fa1001f0001504031042390107a0401d0301545817040250381903815010190401d0001f040310401d0381900015040310401d0002904031030161185c00019040310381503902030c500017040310394102a130001b040310001f0403103819030160381900015040310381504176048150401d03819030e1
|18=>0x10290401d0301604bb5038190401604031032610381600263040310381603a110001b040310381900016040310b81b0403103815040150387a0301500017000160403102ba10101b0401d010160401d03819010190401d03815040150382903016038c500017040310001900017040310381900014040313402503819040152c81b010150401d0381904259458160402503819001ab04814038190403103819
|19=>0x3816030c5000170403102ba30101b0401d03bc1338160401904176048150381904816040190381903a4d010160401d040310401d0381503bbd3401b040150324d010160401d04015032610381602a110001b04031000250381904031040190401503015010170401d038190481403819038150419903829030160b81b0401503815118170001904031038e104816038190401d0001904031010190401d03815
|20=>0x401d0301645816010190401d340270381904015033d50405e0381502bcd0402603819033b9010170401d0001d04031030160481603819040310401d03879030150402503819030161181400019040314581404025038194581704025038190001d0403103015030e10481603819460170001d040314601b0001d040310005e04031038150001b00015040310381900015040310324d010160401d040dd03261
|21=>0x190403103816040e104816038190401d0382903016033dd010140401d0481504019038190001604031038150001f03819040310401904261038160002403819040310381904015030160401d0001404031000190403103815010790401d030154581604025038190124d010160401d048160381904015010190401d04031038190401904015000270381904031040310381903016010790401d030150102b
|22=>0x403100015040310381545817010190401d048150381904016460140001d040310413d00016040310007a04031030150381900019040310481503819040310417603879030150b81b0401d03815029df0001f040310007804031030150107b0401d03015038190001704031048170401d03819000260381904031030b100014040310101b0401d038150401d000160403103be5033b504016033e13401f04015
|23=>0x401d0403102bcf0402603819038193401b040150007b0403103015010140401d03815048160381904031041a904814038190002b04031030164581504025038190005f04031038151001f00015040310393d0001604031458160402503819048150381904015048e1048160381945817040250381901019010150401d0481604025038190001504031038160401d00015040310401d0001b040310401d03819
|24=>0x1500014040310402503819038150401d03819030160401d0001f0403102a130001b04031040e104816038193385e04019038150401903879030150107a0401d030150001f0403103015340260381904015010150401d038197e81f0407903015048160401d0381904bb70381904016458140402503819040190381903815048160381904015048140381904031100230001504031040310407a0301501015
|25=>0x30150381903bb5040160381904015038153402403819040150401603879030152c81b010150401d0403103879030150001b04031038160007904031030150381904016038150401d00017040310001b04031038150002503819040310381904031038150481504025038194581704025038190313d0001604031038b100014040310001f04031030160107a0401d03015040260381903815038190405d03815
|26=>0x387a03015010160401d040310401903261038160005c0403103815000290403103016040190401503816048150401d038190424d010160401d338160401903819010780401d030150401d040310301603a350407a03015038190405e03815040190401503815048150381904015043510b81b038152c81b0405d0381501019010160401d0481704019038191181f0001904031040190387a030150401d04031
|27=>0x301503819040150401d0403100019040310381904016040250381903819030163401f040150381904029030164581404025038194581604025038191001b0001504031048170381904031040310387a03015048170381903016029dd0001f040310002703819040310402d04817038190005d040310381500261040310381645814010190401d040310382903016340270381904015031dd0001f0403104285
|28=>0x3819010160401d04029030160401d030160387903015040190381600015040310401d0301503819038150001b04031338160401904019038150405e038150001d04031040150381603bb504016040150381504031038160001604031040160381504814038190101b0401d040310381500014040310405d0381504816038190407a03015010150401d033b50401604815038193401b040150401d0381904079
|29=>0x401d0301603015038190401504016040190381603815040310481603819010190401d0001f0403104015030160426103816040190401504015030150403103016010140401d040160301504031030150401d03815032610381600017040310b81b0381503819040310402603819040190301504817038190387a030150402503819010170401d0382903016010160401d04019
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xcc00000000006
|6,0=>0x35a80000000000000006650000000030a85c5000000002ba80000000149400004d5090a0000000043507ca0000000000000000000000000000000e540000000068a0000000000000000000000000000000000000000005ea0a9412a8205036a05940000000000000000000000000004540628000
|6,1=>0xd45000000000000cf5194a0000000000018aa00000000c0500002ed45b2800000002c540000ac500000000000000014ea0000512800013aa261449a80000000000000008e50000000044a80000000000042287f5000000000000000000000003d2800000001d543828000000000000000000
|7,0=>0x37286d50d8a000035a86a50d2a1a1433a86650caa191431a86250c2a18142fa85e50baa17142da85a50b2a16142ba80000aca15542a285350a4a000028a850509ea139426a8000098a12d400004a5092a121423a8465000011542228435084a105420283f507ca0f5400003c5076a0e941ca838506ea0d94
|7,1=>0x5128a150000000050289f513ca27544e289b5134a26540000000130a25d4000096512aa251449a8925122a241447a88e50000000046a88c5116a229444a888510ea219442a8845106a209440a880500001fd43f2800000001f543e287b50f4a1e543c287750eca1d543a2873500001c9400007150e0a1bd4
|7,2=>0x6a28d35000000006928d150000341467a8ce519aa33140000cb50000329464a8c8518ea319462a8c45186a309460a8c0517ea00005f28bd5178a2ed40000000174a00005ca8b8516ea2d945aa8b45166a2c9458a8b0500002bd45728ad5158a00000000ab5154a2a545428a750000299452a8a45146a0000
|7,3=>0x1055208a40d40000000204a000080a8000000040147fa8fe51faa3f147da80001f4a3e547c28f75000000000000f6500003d547a28f351e4a3c547828ef51dca3b547628eb51d4a3a547428e750000399472a8e451c6a389470a8e05000037d46f28dd51b8a36d46d28000000036546c28d751aca3554
|7,4=>0x1225242a48148fa91e523aa47140000000236a46948ca918522ea45948aa8000228a44d489291150000441487a90e5000043548628000216a00008529095210a000083a800000004194
|8,0=>0xa94751cea21d413a7c74ece9c1d353a6474bce961d293a4c748ce901d1d3a34745ce8a1d113a1c742ce841d053a0473fce7e1cf939ec73cce781ced39d4739ce721ce139bc736ce6c1cd539a4733ce661cc9398c730ce601cbd397472dce5a1cb1395c72ace541ca53944727ce4e1c99392c724ce481c8d3
|8,1=>0xc14781cf021e013bfc77ecefc1df53be477bcef61de93bcc778cef01ddd3bb4775ceea1dd13b9c772cee41dc53b8476fcede1db93b6c76cced81dad3b54769ced21da13b3c766cecc1d953b24763cec61d893b0c760cec01d7d3af475dceba1d713adc75aceb41d653ac4757ceae1d593aac754cea81d4d3
|8,2=>0xd947b1cf621ec13d7c7aecf5c1eb53d647abcf561ea93d4c7a8cf501e9d3d347a5cf4a1e913d1c7a2cf441e853d0479fcf3e1e793cec79ccf381e6d3cd4799cf321e613cbc796cf2c1e553ca4793cf261e493c8c790cf201e3d3c7478dcf1a1e313c5c78acf141e253c44787cf0e1e193c2c784cf081e0d3
|8,3=>0xddc7bacf741ee53dc47b7cf6e1ed93dac7b4cf681ecd3
|9,0=>0xede5db4bb597692ece5d94bb197612ebe5d74bad97592eae5d54ba997512e9e5d34ba597492e8e5d14ba197412e7e5cf4b9d97392e6e5cd4b9997312e5e5cb4b9597292e4e5c94b9197212e3e5c74b8d97192e2e5c54b8997112e1e5c34b8597092e0e5c14b8197012dfe5bf4b7d96f92dee5bd4b7996f12
|10,0=>0x3bd0f791ef03ddc7bb0f751ee83dcc7b90f711
|11,0=>0x77b0
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
|5,0=>0x400000000000002801
|6,0=>0x8000000000000000001000020000000000000000200000000000000010000000a05c80080000000000000cc000000200000000000000000000000400000004004800000041e000400014000000000000000000000200000000000000040000000000000000000888000000000000000000000000000000000080000000000000a0100000000000000000000000000000000000000004000000000000000000000020000000000000100203f000000000001040000000000000200000000040004000000000000010000200000000000000000000000000000000000000002000000000000040000000000000000000000000000000000000000000000000000000200204080c0008002000820200010000000000000000000000000000000000080c1002080000
|7,0=>0x20200000000000000402000040001400048100000001c000880008000000000000040406700000000800024904092042700022040400018020202016c0000000000100010c0c008984123000101004c0054000a00002e101bc08040202000012000200000008182040e0000000000000700c1200d6d0109a6020000500252c010c0080000080801dc00004400400000004ec0004020830002000020000b800001002e4002008000001000010001200008000080006800040101f800100001020020000c080000001004000002080408000400000021ad90057000214007c0008000000002000104000800208200200000000080000900000004ec0014002100402e0080000001001f008418015c00142090b110260085c00081017300001200210000000100012000040080800009
|7,1=>0x40040811017000000000000080000000050000000000004100002e00010002c0001909206000000004000010002000020000000000000000000400000001000010880800000800a0000c0040cd400980010004e60002020308000800020040400000100136000040060001a0001120020100ac00001001b002c150c5c00040000800020000000000200770000200860c03780060024260800000000000000036004500000000080004000864001000060000000004400000012b000120004000080000a20020204b400500000a800080002480040000060804204000004880080000000000a01b80000000400002003001000800080002800008000100002800044000000253020260085c1004000000000000080000a02009200111034c00001000900010080cc000400000
|7,2=>0x20002080004000100002000040001400000000000008000110008080030010c01010004000000000040002000008008600000000200100002184000000017000be0000000040000000010002c0000080000000220000000000003b
|8,0=>0x100b6001fc091f8213f980de001fc409f8213f080ee001fc003f9005f0008010cfc01bd8423b00080981a000bf8003f000b000180092d9037b6007f800bc01bf808584c080009ec413f8037b40c76981a0009f80917204f6084dc009f900085006e008ec920dc200f004f6180dc441f8065800050101fc003fa6820086dec087c441d9001b5001f401fc030c0013f000fe005fd40846080f5127e4006d003f82010000fe00040400f8403f4007e004fc016c200480027e821c0013d80850010e000ae110078023b0047600dec911b80218000fe2a0dc80bd8007f000fe181a10030440578827e200fc000c0807b200f6008ec04bfc204f0809e300bc24818023b4801e018ef04378c0400c080080fc813f9003b000b0104bc00b59007f8007f0002304040c873202f6088fc002c08008
|8,1=>0x5003e021fc00040037b400ee080fd003f9007b60410004fc019d8125b81090100bc00841041b0406f0013c143d9437f024f6220ed301040077000fe005fe003f820370907e024ec009d8402f0027e0012104a18063b01297085fc201fa013f100fe005ec402c0013f200b000ced201f9433f20030c0029201f80068010a0088eca02d9005c0406e9009c009f8027bc1041801fe800f9027b000fe100fc049d8011020038004fe60040013f40040801fd04302493f
|9,0=>0x400df8203c810f88977100fe224bc00b78007f000fe0a5dc10bfc417f0407e40d7c209fa003f4004e0a5bd00bb8213fc105f0053c20178007f4107f0017c403fc007f0027e021fc81bfc217f4827e4087c003f8497f0827e00aec403f8407f002fe001fc013d8406f000ff0003c20bf9005b0027e001fc109fcc06f0407e981bc409fe003f0027ea05fe001f8063b400ff820fd003f8813f
|10,0=>0x2001f8007f042fe800fc40bf8007f0107e001fc20bf8003f
|11,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 19 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_250,10,runOps true dom_250 (0,roots_250) ops)] else [])++(if pm.testBit 1 then [(dom_249,10,runOps true dom_249 (0,roots_249) ops)] else [])++(if pm.testBit 2 then [(dom_235,10,runOps true dom_235 (0,roots_235) ops)] else [])++(if pm.testBit 3 then [(dom_219,9,runOps true dom_219 (0,roots_219) ops)] else [])++(if pm.testBit 4 then [(dom_187,9,runOps true dom_187 (0,roots_187) ops)] else [])++(if pm.testBit 5 then [(dom_123,9,runOps true dom_123 (0,roots_123) ops)] else [])++(if pm.testBit 6 then [(dom_243,8,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 7 then [(dom_171,8,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 8 then [(dzo_243_8,7,runOps true dzo_243_8 (0,roots_243) ops)] else [])++(if pm.testBit 9 then [(dzo_235_16,7,runOps true dzo_235_16 (0,roots_235) ops)] else [])++(if pm.testBit 10 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 11 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 12 then [(dom_227,6,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 13 then [(dom_211,6,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 14 then [(dom_179,6,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 15 then [(dom_115,6,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 16 then [(dom_107,6,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 17 then [(dom_155,6,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 18 then [(dom_59,6,runOps true dom_59 (0,roots_59) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_251 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_250 _ g hchk
    · exact cpcs (by decide +kernel) low_249 _ g hchk
    · exact cpcs (by decide +kernel) low_235 _ g hchk
    · exact cpcs (by decide +kernel) low_219 _ g hchk
    · exact cpcs (by decide +kernel) low_187 _ g hchk
    · exact cpcs (by decide +kernel) low_123 _ g hchk
    · exact cpcs (by decide +kernel) low_243 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_243_8_161 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_235_16_67 _ g hchk
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) low_91 _ g hchk
    · exact cpcs (by decide +kernel) low_227 _ g hchk
    · exact cpcs (by decide +kernel) low_211 _ g hchk
    · exact cpcs (by decide +kernel) low_179 _ g hchk
    · exact cpcs (by decide +kernel) low_115 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) low_155 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_250 10 s (0, roots_250) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_250 h

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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_120 : ∀ i, 120 ≤ i → i < 126 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 120 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 126 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108) z6_120)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_288 : ∀ i, 288 ≤ i → i < 295 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 288 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 295 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72) z7_84) z7_96) z7_108) z7_120) z7_132) z7_144) z7_156) z7_168) z7_180) z7_192) z7_204) z7_216) z7_228) z7_240) z7_252) z7_264) z7_276) z7_288)
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
private theorem z8 : ∀ i, 0 ≤ i → i < 204 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_12) z8_24) z8_36) z8_48) z8_60) z8_72) z8_84) z8_96) z8_108) z8_120) z8_132) z8_144) z8_156) z8_168) z8_180) z8_192)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 12 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_12 : ∀ i, 12 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_24 : ∀ i, 24 ≤ i → i < 36 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_36 : ∀ i, 36 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_48 : ∀ i, 48 ≤ i → i < 60 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_60 : ∀ i, 60 ≤ i → i < 64 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 60 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 64 → Z 9 i = true := (range_split (range_split (range_split (range_split (range_split z9_0 z9_12) z9_24) z9_36) z9_48) z9_60)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
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

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [4, 7] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [6, 9] }, { op := GateOp.and, inputs := [8, 10] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.and, inputs := [12, 13] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [7, 15] }, { op := GateOp.and, inputs := [3, 16] }, { op := GateOp.and, inputs := [2, 6] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [17, 19] }, { op := GateOp.or, inputs := [18, 20] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_31209_aux

theorem PEqualNP.Outside.L_meta_31209 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_31209_aux.main
