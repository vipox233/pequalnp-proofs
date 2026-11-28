import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30859_aux
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
def goal_255 : Nat := 0xfffffffffffffffffffffffffffefffaffffffffffeeffeefefefefeeeccaa00
def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0e0f0a0f0f0f0f0f0e0f0e0e0e0e0e0e0c0a00
def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_243 : Nat := 0xf000f000f000f000f000f000e000a000f000f000e000e000e000e000c0000
def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_227 : Nat := 0xf0000000f0000000f0000000a0000000f0000000e0000000e00000000
def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_225 : Nat := 0x300000003000000030000000200000003000000020000000200000000
def dom_224 : Nat := 0x100000001000000010000000100000001000000010000000100000001
def roots_224 : List Nat := [xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_224 : Nat := 0x100000001000000010000000000000001000000000000000000000000
def dom_193 : Nat := 0x3000000000000000300000000000000030000000000000003
def roots_193 : List Nat := [xs256.getD 0 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_193 : Nat := 0x3000000000000000200000000000000020000000000000000
def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_161 : Nat := 0x30000000200000000000000000000000200000000
def dom_97 : Nat := 0x3000000030000000300000003
def roots_97 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_97 : Nat := 0x3000000020000000200000000
def goal_227_l2 : Nat := 0xf0000000f0000000f0000000e0000000f0000000e0000000e0000000c
def dzo_227_16 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000
def gzo_227_16_2 : Nat := 0xf0000000f0000000f0000000e0000000f0000000e0000000e0000000c0000
def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_242 : Nat := 0x5000500050005000500050004000000050005000400040004000400040000
def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_226 : Nat := 0x500000005000000050000000000000005000000040000000400000000
def goal_226_l2 : Nat := 0x500000005000000050000000400000005000000040000000400000004
def dzo_226_16 : Nat := 0x5000000050000000500000005000000050000000500000005000000050000
def gzo_226_16_2 : Nat := 0x5000000050000000500000004000000050000000400000004000000040000
def dom_114 : Nat := 0x50005000500050005000500050005
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_114 : Nat := 0x50005000400040004000400040000
def dom_98 : Nat := 0x5000000050000000500000005
def roots_98 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_98 : Nat := 0x5000000040000000400000000
def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_210 : Nat := 0x50005000000000004000000000000000400040000000000040000
def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_178 : Nat := 0x500050004000000000000000000000004000400040000
def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_211 : Nat := 0xf000f00000000000e000a00000000000e000e00000000000c0000
def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_195 : Nat := 0xf000000000000000a000000000000000e0000000000000000
def goal_195_l2 : Nat := 0xf000000000000000e000000000000000e000000000000000c
def dzo_195_16 : Nat := 0xf000000000000000f000000000000000f000000000000000f0000
def gzo_195_16_2 : Nat := 0xf000000000000000e000000000000000e000000000000000c0000
def dom_83 : Nat := 0xf000f00000000000f000f
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_83 : Nat := 0xe000e00000000000c0000
def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_179 : Nat := 0xf000f000e000a0000000000000000000e000e000c0000
def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_163 : Nat := 0xf0000000a00000000000000000000000e00000000
def goal_163_l2 : Nat := 0xf0000000e00000000000000000000000e0000000c
def dzo_163_16 : Nat := 0xf0000000f00000000000000000000000f0000000f0000
def gzo_163_16_2 : Nat := 0xf0000000e00000000000000000000000e0000000c0000
def dom_51 : Nat := 0xf000f000f000f
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_51 : Nat := 0xe000e000c0000
def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_115 : Nat := 0xf000f000e000e000e000e000c0000
def dom_99 : Nat := 0xf0000000f0000000f0000000f
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_99 : Nat := 0xf0000000e0000000e00000000
def goal_99_l2 : Nat := 0xf0000000e0000000e0000000c
def dzo_99_16 : Nat := 0xf0000000f0000000f0000000f0000
def gzo_99_16_2 : Nat := 0xf0000000e0000000e0000000c0000
def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_235 : Nat := 0xf0f00000f0f00000f0f00000f0a00000f0f00000f0e00000e0e00000a00
def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_233 : Nat := 0x30300000303000003030000030200000303000003020000020200000200
def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_203 : Nat := 0xf0f0000000000000f0a0000000000000f0e0000000000000a00
def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_201 : Nat := 0x303000000000000030200000000000003020000000000000200
def dom_200 : Nat := 0x101000000000000010100000000000001010000000000000101
def roots_200 : List Nat := [xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_200 : Nat := 0x101000000000000010000000000000001000000000000000000
def dom_137 : Nat := 0x30300000000000000000000000000000303
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_137 : Nat := 0x30200000000000000000000000000000200
def dom_73 : Nat := 0x3030000000000000303
def roots_73 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0]
def goal_73 : Nat := 0x3020000000000000200
def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_234 : Nat := 0x50500000505000005050000050000000505000005040000040400000000
def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_232 : Nat := 0x10100000101000001010000010000000101000001000000000000000000
def dom_202 : Nat := 0x505000000000000050500000000000005050000000000000505
def roots_202 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_202 : Nat := 0x505000000000000050000000000000005040000000000000000
def dom_106 : Nat := 0x505000005050000050500000505
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_106 : Nat := 0x505000005040000040400000000
def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_171 : Nat := 0xf0f00000f0a000000000000000000000e0e00000a00
def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_169 : Nat := 0x3030000030200000000000000000000020200000200
def goal_169_l32 : Nat := 0x3030000030200000000000000000000030300000200
def dzo_169_2 : Nat := 0xc0c00000c0c000000000000000000000c0c00000c0c
def gzo_169_2_32 : Nat := 0xc0c00000c08000000000000000000000c0c00000800
def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_170 : Nat := 0x5050000050000000000000000000000040400000000
def dom_43 : Nat := 0xf0f00000f0f
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_43 : Nat := 0xe0e00000a00
def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_107 : Nat := 0xf0f00000f0e00000e0e00000a00
def dom_105 : Nat := 0x303000003030000030300000303
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_105 : Nat := 0x303000003020000020200000200
def dom_75 : Nat := 0xf0f0000000000000f0f
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]
def goal_75 : Nat := 0xf0e0000000000000a00
def goal_233_l96 : Nat := 0x30300000303000003030000030200000303000003030000030300000200
def goal_201_l64 : Nat := 0x303000000000000030200000000000003030000000000000200
def dzo_233_2 : Nat := 0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def gzo_233_2_96 : Nat := 0xc0c00000c0c00000c0c00000c0800000c0c00000c0c00000c0c00000800
def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_219 : Nat := 0xf0f0f0f000000000f0e0f0a000000000f0e0f0e000000000e0c0a00
def goal_203_l2 : Nat := 0xf0f0000000000000f0e0000000000000f0e0000000000000e0c
def dzo_203_16 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000
def gzo_203_16_2 : Nat := 0xf0f0000000000000f0e0000000000000f0e0000000000000e0c0000
def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_218 : Nat := 0x5050505000000000504050000000000050405040000000004040000
def goal_202_l2 : Nat := 0x505000000000000050400000000000005040000000000000404
def dzo_202_16 : Nat := 0x5050000000000000505000000000000050500000000000005050000
def gzo_202_16_2 : Nat := 0x5050000000000000504000000000000050400000000000004040000
def dom_90 : Nat := 0x50505050000000005050505
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_90 : Nat := 0x50405040000000004040000
def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]
def goal_91 : Nat := 0xf0e0f0e000000000e0c0a00
def goal_75_l2 : Nat := 0xf0e0000000000000e0c
def dzo_75_16 : Nat := 0xf0f0000000000000f0f0000
def gzo_75_16_2 : Nat := 0xf0e0000000000000e0c0000
def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_155 : Nat := 0xf0e0f0a0000000000000000000000000e0c0a00
def dom_153 : Nat := 0x303030300000000000000000000000003030303
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_153_l16 : Nat := 0x303030200000000000000000000000003030200
def dzo_153_2 : Nat := 0xc0c0c0c0000000000000000000000000c0c0c0c
def gzo_153_2_16 : Nat := 0xc0c0c080000000000000000000000000c0c0800
def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_250 : Nat := 0x505050505050505050505050504050005050505050405040404040404040000
def goal_234_l2 : Nat := 0x50500000505000005050000050400000505000005040000040400000404
def dzo_234_16 : Nat := 0x505000005050000050500000505000005050000050500000505000005050000
def gzo_234_16_2 : Nat := 0x505000005050000050500000504000005050000050400000404000004040000
def dom_122 : Nat := 0x5050505050505050505050505050505
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_122 : Nat := 0x5050505050405040404040404040000
def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_186 : Nat := 0x50505050504050000000000000000000404040404040000
def goal_235_l2 : Nat := 0xf0f00000f0f00000f0f00000f0e00000f0f00000f0e00000e0e00000e0c
def dzo_235_16 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16_2 : Nat := 0xf0f00000f0f00000f0f00000f0e00000f0f00000f0e00000e0e00000e0c0000
def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]
def goal_123 : Nat := 0xf0f0f0f0f0e0f0e0e0e0e0e0e0c0a00
def goal_107_l2 : Nat := 0xf0f00000f0e00000e0e00000e0c
def dzo_107_16 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def gzo_107_16_2 : Nat := 0xf0f00000f0e00000e0e00000e0c0000
def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_59 : Nat := 0xe0e0e0e0e0c0a00
def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_187 : Nat := 0xf0f0f0f0f0e0f0a00000000000000000e0e0e0e0e0c0a00
def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_249_l112 : Nat := 0x303030303030303030303030303030203030303030303030303030303030200
def dzo_249_2 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def gzo_249_2_112 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c080c0c0c0c0c0c0c0c0c0c0c0c0c0c0800

namespace S_224
def pairsG : List (Nat × Nat) := [(32,96), (32,160), (64,96), (64,192), (128,160), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_224.map (· &&& dom_224)
def goalM : Nat := goal_224 &&& dom_224
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x6d565
|3,0=>0x6d565
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x4000000040000000400000004000000000000000000000000000000020000000200000000000000000000000200000002000000000000000100000000000000010000000000000001000000000000000100000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 225 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_224 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_224 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000, 96), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff00000000ffffffff00000000, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_224 == dom_224) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_224 goalM v ys) : RunD true dom_224 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_224 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_224 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_224 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_224 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_224 roots_224 goal_224 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_224

theorem low_224 : Lower true dom_224 roots_224 goal_224 4 := S_224.noCircuit

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

namespace S_97
def pairsG : List (Nat × Nat) := [(1,33), (1,65), (32,33), (32,96), (64,65), (64,96)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_97.map (· &&& dom_97)
def goalM : Nat := goal_97 &&& dom_97
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xa6263
|3,0=>0xa6263
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3000000030000000000000000c000000000000000c00000002000000020000000200000002
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 98 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_97 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_97 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_97 == dom_97) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_97 goalM v ys) : RunD true dom_97 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_97 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_97 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_97 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_97 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_97 roots_97 goal_97 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_97

theorem low_97 : Lower true dom_97 roots_97 goal_97 4 := S_97.noCircuit

namespace S_225
def pairsG : List (Nat × Nat) := [(1,33), (1,65), (1,129), (32,33), (32,96), (32,160), (64,65), (64,96), (64,192), (128,129), (128,160), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_225.map (· &&& dom_225)
def goalM : Nat := goal_225 &&& dom_225
def NN : Nat → Nat
|3=>0x3
|4=>0x3
|5=>0x2
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x2e9822932128eb9
|4,0=>0x6f62d3132f29c55
|5,0=>0x4f3850f361
|6,0=>0xf361
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xc0000000c0000000c000000080000000c0000000c0000000c0000000800000000000000000000000000000003000000020000000300000002c0000000c0000000c000000000000000c0000000c0000000c0000000000000003000000000000000300000000000000030000000000000002c0000000c00000000000000000000000c0000000c000000000000000300000003000000020000000200000003000000030000000200000002c0000000c0000000c0000000c0000000c0000000c000000000000000300000003000000030000000300000002000000020000000200000002c000000000000000c000000000000000c000000000000000c0000000200000002000000020000000200000002000000020000000200000002c0000000c0000000c0000000c0000000000000000000000000000000300000003000000000000000000000003000000020000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x17321273917321327b7321a23915721836543210
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x8411004
|4,0=>0x165454c5
|5,0=>0x7d5b4
|6,0=>0x244
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 12 then fld (dictB (i / 512) (i / 32 % 16)) 226 (i % 32) else 0
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
|0=>0x7345d374491749d
|_=>0
def opOffB : Nat → Nat → Nat
|3,0=>0x180
|4,0=>0x32
|5,0=>0x28d0
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
|3,0=>0x50
|4,0=>0xa
|5,0=>0xf7
|6,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 4 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_224,4,runOps true dom_224 (0,roots_224) ops)] else [])++(if pm.testBit 1 then [(dom_193,4,runOps true dom_193 (0,roots_193) ops)] else [])++(if pm.testBit 2 then [(dom_161,4,runOps true dom_161 (0,roots_161) ops)] else [])++(if pm.testBit 3 then [(dom_97,4,runOps true dom_97 (0,roots_97) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_225 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_224 _ g hchk
    · exact cpcs (by decide +kernel) low_193 _ g hchk
    · exact cpcs (by decide +kernel) low_161 _ g hchk
    · exact cpcs (by decide +kernel) low_97 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_224 4 s (0, roots_224) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_225 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_224 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000, 96), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff00000000ffffffff00000000, 96)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xffffffffffffffff0000000000000000, 64)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xffffffff00000000ffffffff00000000, 96)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_225 == dom_225) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_225 goalM v ys) : RunD true dom_225 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_225 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_225 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_225 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_225 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_225 roots_225 goal_225 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_225

theorem low_225 : Lower true dom_225 roots_225 goal_225 7 := S_225.noCircuit

theorem low_227 : Lower true dom_227 roots_227 goal_227 8 :=
  lower_slice (d:=dom_227) (dSub:=dom_225) (T:=goal_227) (TSub:=goal_225) (roots:=roots_227) (rootsSub:=roots_225)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c0000000c0000000c0000000c0000000c0000000c0000000c, 32, 34)] (by decide +kernel) (by decide +kernel) low_225

theorem low_227_l2 : Lower true dom_227 roots_227 goal_227_l2 8 :=
  lower_slice (d:=dom_227) (dSub:=dom_225) (T:=goal_227_l2) (TSub:=goal_225) (roots:=roots_227) (rootsSub:=roots_225)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c0000000c0000000c0000000c0000000c0000000c0000000c, 0, 2)] (by decide +kernel) (by decide +kernel) low_225

theorem lowZ_227_16_2 : Lower true dzo_227_16 roots_227 gzo_227_16_2 8 :=
  lower_iso (d1:=dom_227) (roots1:=roots_227) (T1:=goal_227_l2) [(dom_227, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_227_l2

theorem low_226 : Lower true dom_226 roots_226 goal_226 5 :=
  lower_slice (d:=dom_226) (dSub:=dom_224) (T:=goal_226) (TSub:=goal_224) (roots:=roots_226) (rootsSub:=roots_224)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x400000004000000040000000400000004000000040000000400000004, 32, 34)] (by decide +kernel) (by decide +kernel) low_224

theorem low_226_l2 : Lower true dom_226 roots_226 goal_226_l2 5 :=
  lower_slice (d:=dom_226) (dSub:=dom_224) (T:=goal_226_l2) (TSub:=goal_224) (roots:=roots_226) (rootsSub:=roots_224)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x400000004000000040000000400000004000000040000000400000004, 0, 2)] (by decide +kernel) (by decide +kernel) low_224

theorem lowZ_226_16_2 : Lower true dzo_226_16 roots_226 gzo_226_16_2 5 :=
  lower_iso (d1:=dom_226) (roots1:=roots_226) (T1:=goal_226_l2) [(dom_226, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_226_l2

namespace S_98
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (32,34), (32,96), (64,66), (64,96)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_98.map (· &&& dom_98)
def goalM : Nat := goal_98 &&& dom_98
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xd981e
|3,0=>0xd981e
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140000001400000000000000028000000000000002800000004000000040000000400000004
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 99 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_98 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_98 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_98 == dom_98) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_98 goalM v ys) : RunD true dom_98 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_98 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_98 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_98 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_98 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_98 roots_98 goal_98 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_98

theorem low_98 : Lower true dom_98 roots_98 goal_98 4 := S_98.noCircuit

theorem low_114 : Lower true dom_114 roots_114 goal_114 5 :=
  lower_slice (d:=dom_114) (dSub:=dom_98) (T:=goal_114) (TSub:=goal_98) (roots:=roots_114) (rootsSub:=roots_98)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50000000500000005000000050000, 2, 18)] (by decide +kernel) (by decide +kernel) low_98

namespace S_210
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (16,18), (64,66), (64,192), (80,82), (80,208), (128,192), (130,146), (130,194), (144,146), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_210.map (· &&& dom_210)
def goalM : Nat := goal_210 &&& dom_210
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xf0541
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa000a00000000000a000a0000000000000000000000000000000140014000000000000000000000000001400140000000000000002800000000000000280000000000000028000000000000002800040004000000000004000400000000000400040000000000040004
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 211 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_210 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_210 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xffff0000ffff0000ffff0000ffff0000, 112)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_210 == dom_210) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_210 goalM v ys) : RunD true dom_210 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_210 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_210 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_210 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_210 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_210 roots_210 goal_210 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_210

theorem low_210 : Lower true dom_210 roots_210 goal_210 4 := S_210.noCircuit

namespace S_178
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (16,18), (32,34), (32,160), (48,50), (48,176), (128,160), (130,146), (130,162), (144,146), (144,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_178.map (· &&& dom_178)
def goalM : Nat := goal_178 &&& dom_178
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x36af8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa000a000a000a0000000000000000000000000000000140014000000000000000000000000001400140000000280000002800000000000000000000002800000028000400040004000400000000000000000004000400040004
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 179 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_178 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_178 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff0000ffff0000ffff0000ffff0000, 112)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_178 == dom_178) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_178 goalM v ys) : RunD true dom_178 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_178 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_178 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_178 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_178 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_178 roots_178 goal_178 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_178

theorem low_178 : Lower true dom_178 roots_178 goal_178 4 := S_178.noCircuit

namespace S_242
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,66), (16,18), (32,34), (32,96), (32,160), (48,50), (48,112), (48,176), (64,66), (64,96), (64,192), (80,82), (80,112), (80,208), (128,160), (128,192), (130,146), (130,162), (130,194), (144,146), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_242.map (· &&& dom_242)
def goalM : Nat := goal_242 &&& dom_242
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xad794
|5,0=>0xae6ff
|6,0=>0xd0973
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x140014001400140014001400140014000000000000000000000000000000028002800280028002800280000000000280028002800280028002800000005000000050000000500000005000000050000000500000005000000050000800080008000800080008000800080008000800080008000800080008000940014001400140000000000000000001400140014001400000000000000028002800000000002800280000000000280028000000000028002800000000000000000000000000000000000000050005000500050005000500000000
|_,_=>0
def stPool : Nat → Nat
|0=>0xc8c7a346c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 243 (i % 32) else 0
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
|6,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 1 then [(dzo_226_16,5,runOps true dzo_226_16 (0,roots_226) ops)] else [])++(if pm.testBit 2 then [(dom_114,5,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 3 then [(dom_224,4,runOps true dom_224 (0,roots_224) ops)] else [])++(if pm.testBit 4 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 5 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_242 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_226 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_226_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) low_224 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_226 5 s (0, roots_226) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_242 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_226 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_242 == dom_242) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_242 goalM v ys) : RunD true dom_242 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_242 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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

theorem low_195 : Lower true dom_195 roots_195 goal_195 5 :=
  lower_slice (d:=dom_195) (dSub:=dom_193) (T:=goal_195) (TSub:=goal_193) (roots:=roots_195) (rootsSub:=roots_193)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000000000000000c000000000000000c000000000000000c, 64, 66)] (by decide +kernel) (by decide +kernel) low_193

theorem low_195_l2 : Lower true dom_195 roots_195 goal_195_l2 5 :=
  lower_slice (d:=dom_195) (dSub:=dom_193) (T:=goal_195_l2) (TSub:=goal_193) (roots:=roots_195) (rootsSub:=roots_193)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000000000000000c000000000000000c000000000000000c, 0, 2)] (by decide +kernel) (by decide +kernel) low_193

theorem lowZ_195_16_2 : Lower true dzo_195_16 roots_195 gzo_195_16_2 5 :=
  lower_iso (d1:=dom_195) (roots1:=roots_195) (T1:=goal_195_l2) [(dom_195, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_195_l2

namespace S_83
def pairsG : List (Nat × Nat) := [(1,65), (2,18), (2,66), (3,19), (3,67), (16,18), (17,19), (17,81), (64,65), (64,66), (80,81), (80,82)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_83.map (· &&& dom_83)
def goalM : Nat := goal_83 &&& dom_83
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xbce70
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f0000000000000000f000000000000000f0000c000c00000000000c000ca000a00000000000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 84 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_83 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_83 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
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

theorem low_83 : Lower true dom_83 roots_83 goal_83 4 := S_83.noCircuit

namespace S_211
def pairsG : List (Nat × Nat) := [(1,65), (1,129), (2,18), (2,66), (3,19), (3,67), (3,131), (16,18), (17,19), (17,81), (17,145), (64,65), (64,66), (64,192), (80,81), (80,82), (80,208), (128,129), (128,192), (130,131), (130,146), (130,194), (144,145), (144,146), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x5f9f828cac
|5,0=>0x676bc38d3027bde
|6,0=>0xc2467
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000f000f0000000000000000f000f00000000000f000f00000000000000000000000000000000f000f00000000000f000f00000000000a000a00000000000a000a00000000000000000000000000000000f000f00000000000a000af000000000000000f000000000000000f000000000000000f0000c000c00000000000c000c00000000000c000c00000000000c000cf000f000000000000000000000000000f000f0000000000000000a000a00000000000a000a00000000000a000a00000000000a000af000f00000000000a000a00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x724311432791432782437164321543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 212 (i % 32) else 0
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
|0=>0x9d27dc5
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
|6,0=>0x1e
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_195,5,runOps true dom_195 (0,roots_195) ops)] else [])++(if pm.testBit 1 then [(dzo_195_16,5,runOps true dzo_195_16 (0,roots_195) ops)] else [])++(if pm.testBit 2 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 3 then [(dom_193,4,runOps true dom_193 (0,roots_193) ops)] else [])++(if pm.testBit 4 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_211 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_195 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_195_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_193 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_195 5 s (0, roots_195) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_195 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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

theorem low_211 : Lower true dom_211 roots_211 goal_211 7 := S_211.noCircuit

theorem low_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_slice (d:=dom_163) (dSub:=dom_161) (T:=goal_163) (TSub:=goal_161) (roots:=roots_163) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c00000000000000000000000c0000000c, 32, 34)] (by decide +kernel) (by decide +kernel) low_161

theorem low_163_l2 : Lower true dom_163 roots_163 goal_163_l2 5 :=
  lower_slice (d:=dom_163) (dSub:=dom_161) (T:=goal_163_l2) (TSub:=goal_161) (roots:=roots_163) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c00000000000000000000000c0000000c, 0, 2)] (by decide +kernel) (by decide +kernel) low_161

theorem lowZ_163_16_2 : Lower true dzo_163_16 roots_163 gzo_163_16_2 5 :=
  lower_iso (d1:=dom_163) (roots1:=roots_163) (T1:=goal_163_l2) [(dom_163, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_163_l2

namespace S_51
def pairsG : List (Nat × Nat) := [(1,33), (2,18), (2,34), (3,19), (3,35), (16,18), (17,19), (17,49), (32,33), (32,34), (48,49), (48,50)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x5ac2a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f00000000f0000000f0000c000c000c000ca000a000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 52 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_51 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_51 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_51 goalM v ys) : RunD true dom_51 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_51 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_51 roots_51 goal_51 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_51

theorem low_51 : Lower true dom_51 roots_51 goal_51 4 := S_51.noCircuit

namespace S_179
def pairsG : List (Nat × Nat) := [(1,33), (1,129), (2,18), (2,34), (3,19), (3,35), (3,131), (16,18), (17,19), (17,49), (17,145), (32,33), (32,34), (32,160), (48,49), (48,50), (48,176), (128,129), (128,160), (130,131), (130,146), (130,162), (144,145), (144,146), (144,176)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_179.map (· &&& dom_179)
def goalM : Nat := goal_179 &&& dom_179
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x74ad409e5e
|5,0=>0xb432d57d9d53fba
|6,0=>0x1d437
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf000f00000000f000f000f000f0000000000000000000f000f00000000f000f000f000f00000000000000000000000000000000f000f000f000f0000000000000000000a000a000a000af000f000a000a00000000000000000000000000000000f0000000f00000000000000000000000f0000000f0000c000c000c000c0000000000000000000c000c000c000cf000f000000000000000000000000000f000f00000000a000a000a000a0000000000000000000a000a000a000a00000000000000000000000000000000f000f000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0x724311432791432782437164321543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 180 (i % 32) else 0
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
|0=>0x9f275c5
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
|5,0=>0x4e04
|6,0=>0x1e
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 1 then [(dzo_163_16,5,runOps true dzo_163_16 (0,roots_163) ops)] else [])++(if pm.testBit 2 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 3 then [(dom_161,4,runOps true dom_161 (0,roots_161) ops)] else [])++(if pm.testBit 4 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_179 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_163_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_161 _ g hchk
    · exact cpcs (by decide +kernel) low_51 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_163 5 s (0, roots_163) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_179 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_163 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_179 == dom_179) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_179 goalM v ys) : RunD true dom_179 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_179 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_179 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_179 roots_179 goal_179 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_179

theorem low_179 : Lower true dom_179 roots_179 goal_179 7 := S_179.noCircuit

theorem low_99 : Lower true dom_99 roots_99 goal_99 5 :=
  lower_slice (d:=dom_99) (dSub:=dom_98) (T:=goal_99) (TSub:=goal_98) (roots:=roots_99) (rootsSub:=roots_98)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0000000a0000000a0000000a, 32, 33)] (by decide +kernel) (by decide +kernel) low_98

theorem low_99_l2 : Lower true dom_99 roots_99 goal_99_l2 5 :=
  lower_slice (d:=dom_99) (dSub:=dom_97) (T:=goal_99_l2) (TSub:=goal_97) (roots:=roots_99) (rootsSub:=roots_97)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c0000000c0000000c, 0, 2)] (by decide +kernel) (by decide +kernel) low_97

theorem lowZ_99_16_2 : Lower true dzo_99_16 roots_99 gzo_99_16_2 5 :=
  lower_iso (d1:=dom_99) (roots1:=roots_99) (T1:=goal_99_l2) [(dom_99, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_99_l2

namespace S_115
def pairsG : List (Nat × Nat) := [(1,33), (1,65), (2,18), (2,34), (2,66), (3,19), (3,35), (3,67), (16,18), (17,19), (17,49), (17,81), (32,33), (32,34), (32,96), (48,49), (48,50), (48,112), (64,65), (64,66), (64,96), (80,81), (80,82), (80,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_115.map (· &&& dom_115)
def goalM : Nat := goal_115 &&& dom_115
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x8cc4c
|5,0=>0x94146
|6,0=>0xb0387
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa000a000a000a000a000a000a000af000f000f000f000f000f00000000f0000000f0000000f0000000f0000c000c000c000c000c000c000c000cf000f000f000f0000000000000000f000f00000000000f000f0000000050005000500050005000500000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x463d1e46c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 116 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_114,5,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 1 then [(dom_99,5,runOps true dom_99 (0,roots_99) ops)] else [])++(if pm.testBit 2 then [(dzo_99_16,5,runOps true dzo_99_16 (0,roots_99) ops)] else [])++(if pm.testBit 3 then [(dom_97,4,runOps true dom_97 (0,roots_97) ops)] else [])++(if pm.testBit 4 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 5 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_115 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) low_99 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_99_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_97 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
    · exact cpcs (by decide +kernel) low_51 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_114 5 s (0, roots_114) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_115 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_114 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_115 == dom_115) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_115 goalM v ys) : RunD true dom_115 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_115 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_115 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_115 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_115 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_115 roots_115 goal_115 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_115

theorem low_115 : Lower true dom_115 roots_115 goal_115 7 := S_115.noCircuit

namespace S_243
def pairsG : List (Nat × Nat) := [(1,33), (1,65), (1,129), (2,18), (2,34), (2,66), (3,19), (3,35), (3,67), (3,131), (16,18), (17,19), (17,49), (17,81), (17,145), (32,33), (32,34), (32,96), (32,160), (48,49), (48,50), (48,112), (48,176), (64,65), (64,66), (64,96), (64,192), (80,81), (80,82), (80,112), (80,208), (128,129), (128,160), (128,192), (130,131), (130,146), (130,162), (130,194), (144,145), (144,146), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_243.map (· &&& dom_243)
def goalM : Nat := goal_243 &&& dom_243
def NN : Nat → Nat
|4=>0x3
|5=>0xf
|6=>0x23
|7=>0xf
|8=>0x3
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x3dda22227513f03
|5,0=>0xed3f6c8af2b307c9a97e9762f721d06a340657e96503d46a632bf0b2689c180a308a6406205
|6,0=>0xd2b9bc8af2bf0bcaf1757407569172621d75305751ce7493c841bd64044d38cd83760a2e7cf2d2522c82826da525e8222a8d2132b20b7f1f130154ae1419812b7511ebb11bb20d4280a31b06817050180328702ae4014f8
|7,0=>0xeb807ea311884c487305714806eb47687f14f98d4ee74385713151d28b031ddf91a7b204fe5
|8,0=>0x90dbb3ac1205184
|9,0=>0xaa738
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x50005000500050005000500000000f000f000f000f0000000000000000000f000f000f000f000f000f000a000a000000000000000000000000000000000000000000000000f000f000a000af000f000f000f000f000f000f000f000500050005000500050005000000000000000000000000f000f000f000f0000000000000000000f000f00000000f000f000f000f000f000f000f000f00000000000f000f00000000000a000a5000500050005000500050000000000050005000500050005000500000000f000f000f000f000f000f000a000a000f000f000f000f000f000f000a000a00000000f000f00000000000f000f00000000000f000f00000000000a000a00000000000000000000000000000000f000f000f000f000f000f000a000aa000a000a000a000a000a000a000a000a000a000a000a000a000a0000000000000000000000000000000000000000f000f000a000a000f000f000a000af000f000f000f000a000a000a000a000f000f00000000000a000a000000000000000000000000f000f000a000a0000000000000000000f000f000a000a00000000000000000000000000000000f000f000f000f000f000f00000000f000f000e000e000f000f000e000e000f000f000e000e000c000c000c000cf000f000f000f000f000f000f000f000f000f000f000f000a000a000a000af000f000f000f000f000f000f000f000f000f000f000f0000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000f000f000a000a000f000f000a000a000f000f000a000a000f000f000a000af000f000f000f000f000f000f000f000a000a000a000a000a000a000a000ac000c000c000c000c000c000c000c000c000c000c000c000c000c000c000cf000f000f000f000a000a000a000a000f000f000f000f000a000a000a000af000f000a000a000f000f000a000a000f000f000a000a0000000000000000f000f000f000f000f000f000f000f000f000f00000000000f000f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000f000f000f000f000f000f000f000f00000000000000000000000000000000f000f000f000f000f000f00000000000f000f000f000f000f000f00000000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000af000f000f000f000e000e000e000e000f000f000c000c000e000e000c000c
|0,1=>0xf000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000f000f000f000f000a000a000a000af000f000f000f000f000f000f000f000f000f000a000a000f000f000a000af000f000f000f000f000f000a000a00000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000a000a
|_,_=>0
def stPool : Nat → Nat
|0=>0x34210830334554420d04331704420d30e44420d3c528420c04d58420c2c724420c35154420e14a1c420c24d4c42035070842030814c420524708420d48914420a1c34443010cd4042033ca08420c1c31842032c72842091821081c61440c2040
|1=>0x10834e14128310828708420c3520c90c420c35864420c0cd54420c0d43471080cd6c128420d04331310830524d1c420d04c0da34420524a1080c50811c310828d0991080c534164420d04c1d610834c0c25442010d4342108301358584205049
|2=>0xc420d04c1d834420c04388420c04a0cd3811080c534234420c0c116210830135884420c04d58420c0cd06010834c0425842010cf3021080c134c7c420c0cb04710830d2c124420c04335e1083413cc14420c04335d10834c04370420c04d0d6
|3=>0xcd3042010c420134c08334420c04a34c1080c124420304934c08310830a3471080cd30164c1080470ce34420c14124420334c04264110830334b04420d0cc90420134c0c22cc1083410e3
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de9ad4679fbce1e62f2a791bc71e2af0e783bc01df2ef36763b95dbecd8768bb29d86ebc75b32bdd50ea174d3a4dd18e8573f39ddce0e697
|7,0=>0x706374fb37d63e95f3b1967c7be1e300f788b8bda62c4f5a8
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 37 then fld (dictB (i / 512) (i / 32 % 16)) 244 (i % 32) else 0
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
|0=>0x434c0d0428d31301420734c4c0d0d88c1d3414b040c24d3130d432a301580f34a4c0534c410d303412c3454c0d3ccc31d3414b0f30e4d0d3014c0d04e4d0d0c14d053454c0d1470d050434c0d1470d0534c4c0d34c4d050434c0d34c4c050c74d0528e03353414c053014d053454c0d
|1=>0x343430934c431e3414c1d341432930143353014d313034115303580f34a4c05603c10934c4c350c74d052428d310c14d053454c0d0c14d153034d510ca8c05303413934343650428d3134c4d05301410d34a8c05601cd293014b043454c0d341432a3014c053458c0d14703313414c05
|2=>0x34c4c050c14d310c14d05301410a34c4335341410d303410a34c4d153034c3a
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x1c40001840000001440001040c4000000000084044004
|6,0=>0x6e30006b36836536235f35c35930005630000005335034d34a34734434130000003e30003b33833533232f32c3293263233203
|7,0=>0x8d28b28928728528328127f27d27b2792772752732712
|8,0=>0x9119018f1
|9,0=>0x920
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x10000004000000044000030080000000000010024004
|6,0=>0x300001301000700400402001000004000000003e04030100e02000407e0000000de000014040004053020040080010002821
|7,0=>0xb733c07ea6e4de037c7c81cc5325a3145fe07447a584
|8,0=>0x7e17e0fe
|9,0=>0x7e
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 12 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_227,8,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 1 then [(dzo_227_16,8,runOps true dzo_227_16 (0,roots_227) ops)] else [])++(if pm.testBit 2 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 3 then [(dom_225,7,runOps true dom_225 (0,roots_225) ops)] else [])++(if pm.testBit 4 then [(dom_211,7,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 5 then [(dom_179,7,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 6 then [(dom_115,7,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 7 then [(dom_114,5,runOps true dom_114 (0,roots_114) ops)] else [])++(if pm.testBit 8 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 9 then [(dom_178,4,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 10 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])++(if pm.testBit 11 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_243 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_227 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_227_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_242 _ g hchk
    · exact cpcs (by decide +kernel) low_225 _ g hchk
    · exact cpcs (by decide +kernel) low_211 _ g hchk
    · exact cpcs (by decide +kernel) low_179 _ g hchk
    · exact cpcs (by decide +kernel) low_115 _ g hchk
    · exact cpcs (by decide +kernel) low_114 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
    · exact cpcs (by decide +kernel) low_51 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_227 8 s (0, roots_227) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_243 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_227 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xffffffff000000000000000000000000ffffffff00000000, 32)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_243 == dom_243) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_243 goalM v ys) : RunD true dom_243 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 24 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := (range_split (range_split z6_0 z6_12) z6_24)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_12 : ∀ i, 12 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 12 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := (range_split z7_0 z7_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_243 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_243 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_243 roots_243 goal_243 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_243

theorem low_243 : Lower true dom_243 roots_243 goal_243 10 := S_243.noCircuit

theorem low_233 : Lower true dom_233 roots_233 goal_233 8 :=
  lower_slice (d:=dom_233) (dSub:=dom_225) (T:=goal_233) (TSub:=goal_225) (roots:=roots_233) (rootsSub:=roots_225)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30000000300000003000000030000000300000003000000030000000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_225

namespace S_200
def pairsG : List (Nat × Nat) := [(8,72), (8,136), (64,72), (64,192), (128,136), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_200.map (· &&& dom_200)
def goalM : Nat := goal_200 &&& dom_200
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0x2e51
|3,0=>0x2e51
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x4040000000000000404000000000000000000000000000000020200000000000000000000000000000202000000000000000100000000000000010000000000000001000000000000000100
|_,_=>0
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 201 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_200 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_200 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_200 == dom_200) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_200 goalM v ys) : RunD true dom_200 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_200 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_200 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_200 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_200 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_200 roots_200 goal_200 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_200

theorem low_200 : Lower true dom_200 roots_200 goal_200 4 := S_200.noCircuit

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

namespace S_201
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (8,9), (8,72), (8,136), (64,65), (64,72), (64,192), (128,129), (128,136), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_201.map (· &&& dom_201)
def goalM : Nat := goal_201 &&& dom_201
def NN : Nat → Nat
|3=>0x3
|4=>0x3
|5=>0x2
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x3dc473864600378
|4,0=>0x374e40d6e208fb8
|5,0=>0x346871b461
|6,0=>0x34687
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xc0c0000000000000c080000000000000c0c0000000000000c0803000000000000000300000000000000030000000000000000c0c0000000000000c0c0000000000000c0c000000000000000303000000000000030300000000000003000000000000000300c0c0000000000000c0c0000000000000808000000000000080b02000000000000030200000000000003020000000000000302c0c00000000000000000000000000000c0c000000000000000003000000000000000300000000000000030000000000000002c0c0000000000000c0c000000000000000000000000000000030000000000000003000000000000000300000000000000030080800000000000008080000000000000808000000000000080b03000000000000000000000000000003020000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x35213521213593521b1352a15928587635143210
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x8411004
|4,0=>0x165454c5
|5,0=>0x811b5
|6,0=>0x244
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 12 then fld (dictB (i / 512) (i / 32 % 16)) 202 (i % 32) else 0
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
|0=>0x354c9534853148d
|_=>0
def opOffB : Nat → Nat → Nat
|3,0=>0xc000
|4,0=>0x32
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
|3,0=>0x300
|4,0=>0x6
|5,0=>0x7f
|6,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 4 (j % 128)
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
    · exact cpcs (by decide +kernel) low_200 _ g hchk
    · exact cpcs (by decide +kernel) low_193 _ g hchk
    · exact cpcs (by decide +kernel) low_137 _ g hchk
    · exact cpcs (by decide +kernel) low_73 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_200 4 s (0, roots_200) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_201 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_200 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffffffffffffffff0000000000000000, 64)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_201 == dom_201) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_201 goalM v ys) : RunD true dom_201 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_201 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
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

theorem low_201 : Lower true dom_201 roots_201 goal_201 7 := S_201.noCircuit

theorem low_203 : Lower true dom_203 roots_203 goal_203 8 :=
  lower_slice (d:=dom_203) (dSub:=dom_201) (T:=goal_203) (TSub:=goal_201) (roots:=roots_203) (rootsSub:=roots_201)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) low_201

theorem low_232 : Lower true dom_232 roots_232 goal_232 5 :=
  lower_slice (d:=dom_232) (dSub:=dom_224) (T:=goal_232) (TSub:=goal_224) (roots:=roots_232) (rootsSub:=roots_224)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x10000000100000001000000010000000100000001000000010000000100, 64, 72)] (by decide +kernel) (by decide +kernel) low_224

theorem low_202 : Lower true dom_202 roots_202 goal_202 5 :=
  lower_slice (d:=dom_202) (dSub:=dom_200) (T:=goal_202) (TSub:=goal_200) (roots:=roots_202) (rootsSub:=roots_200)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x404000000000000040400000000000004040000000000000404, 64, 66)] (by decide +kernel) (by decide +kernel) low_200

theorem low_106 : Lower true dom_106 roots_106 goal_106 5 :=
  lower_slice (d:=dom_106) (dSub:=dom_98) (T:=goal_106) (TSub:=goal_98) (roots:=roots_106) (rootsSub:=roots_98)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500000005000000050000000500, 64, 72)] (by decide +kernel) (by decide +kernel) low_98

namespace S_234
def pairsG : List (Nat × Nat) := [(2,34), (2,66), (8,72), (8,136), (10,42), (10,74), (10,138), (32,34), (32,96), (32,160), (40,42), (40,104), (40,168), (64,66), (64,72), (64,96), (64,192), (128,136), (128,160), (128,192), (130,138), (130,162), (130,194)]
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
    (if pm.testBit 0 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 1 then [(dom_226,5,runOps true dom_226 (0,roots_226) ops)] else [])++(if pm.testBit 2 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 3 then [(dom_106,5,runOps true dom_106 (0,roots_106) ops)] else [])
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
    · exact cpcs (by decide +kernel) low_106 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_232 5 s (0, roots_232) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_234 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_232 h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffffffff00000000ffffffff00000000, 96)]]
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

theorem low_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_slice (d:=dom_169) (dSub:=dom_161) (T:=goal_169) (TSub:=goal_161) (roots:=roots_169) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3000000030000000000000000000000030000000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_161

theorem low_169_l32 : Lower true dom_169 roots_169 goal_169_l32 5 :=
  lower_slice (d:=dom_169) (dSub:=dom_137) (T:=goal_169_l32) (TSub:=goal_137) (roots:=roots_169) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030000000000000000000000000000030300000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_137

theorem lowZ_169_2_32 : Lower true dzo_169_2 roots_169 gzo_169_2_32 5 :=
  lower_iso (d1:=dom_169) (roots1:=roots_169) (T1:=goal_169_l32) [(dom_169, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_169_l32

namespace S_170
def pairsG : List (Nat × Nat) := [(2,34), (8,136), (10,42), (10,138), (32,34), (32,160), (40,42), (40,168), (128,136), (128,160), (130,138), (130,162)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_170.map (· &&& dom_170)
def goalM : Nat := goal_170 &&& dom_170
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xae0e2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a00000a0a0000000000000000000000000000000141400000000000000000000000000001414000000028000000280000000000000000000000280000002804040000040400000000000000000000040400000404
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 171 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_170 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_170 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffffffff00000000ffffffff00000000, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_170 == dom_170) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_170 goalM v ys) : RunD true dom_170 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_170 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_170 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_170 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_170 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_170 roots_170 goal_170 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_170

theorem low_170 : Lower true dom_170 roots_170 goal_170 4 := S_170.noCircuit

namespace S_43
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (2,34), (3,11), (3,35), (8,9), (10,11), (10,42), (32,33), (32,34), (40,41), (40,42)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_43.map (· &&& dom_43)
def goalM : Nat := goal_43 &&& dom_43
def NN : Nat → Nat
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x9959f
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f00000000f0000000f00c0c00000c0ca0a00000a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0xe4
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 44 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_43 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_43 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_43 == dom_43) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_43 goalM v ys) : RunD true dom_43 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_43 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_43 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_43 roots_43 goal_43 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_43

theorem low_43 : Lower true dom_43 roots_43 goal_43 4 := S_43.noCircuit

namespace S_171
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,129), (2,34), (3,11), (3,35), (3,131), (8,9), (8,136), (10,11), (10,42), (10,138), (32,33), (32,34), (32,160), (40,41), (40,42), (40,168), (128,129), (128,136), (128,160), (130,131), (130,138), (130,162)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_171.map (· &&& dom_171)
def goalM : Nat := goal_171 &&& dom_171
def NN : Nat → Nat
|4=>0x1
|5=>0x1
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x809ab
|5,0=>0xdceb7
|6,0=>0xb1bca
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0000000f00000000000000000000000f0000000f00f0f00000f0f000000000000000000000a0a00000a0af0f00000000000000000000000000000f0f00000000c0c00000c0c000000000000000000000c0c00000c0cf0f00000f0f00000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a0a00f0000000f00000000000000000000000a0000000a
|_,_=>0
def stPool : Nat → Nat
|0=>0x53333346c688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 7 then fld (dictB (i / 512) (i / 32 % 16)) 172 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 1 then [(dzo_169_2,5,runOps true dzo_169_2 (0,roots_169) ops)] else [])++(if pm.testBit 2 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 3 then [(dom_170,4,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 4 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])++(if pm.testBit 5 then [(dom_43,4,runOps true dom_43 (0,roots_43) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_171 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_169_2_32 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_137 _ g hchk
    · exact cpcs (by decide +kernel) low_43 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_169 5 s (0, roots_169) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_171 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_169 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_171 == dom_171) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_171 goalM v ys) : RunD true dom_171 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_171 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_171 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_171 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_171 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_171 roots_171 goal_171 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_171

theorem low_171 : Lower true dom_171 roots_171 goal_171 7 := S_171.noCircuit

theorem low_105 : Lower true dom_105 roots_105 goal_105 5 :=
  lower_slice (d:=dom_105) (dSub:=dom_97) (T:=goal_105) (TSub:=goal_97) (roots:=roots_105) (rootsSub:=roots_97)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300000003000000030000000300, 1, 9)] (by decide +kernel) (by decide +kernel) low_97

theorem low_75 : Lower true dom_75 roots_75 goal_75 5 :=
  lower_slice (d:=dom_75) (dSub:=dom_73) (T:=goal_75) (TSub:=goal_73) (roots:=roots_75) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) low_73

namespace S_107
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,34), (2,66), (3,11), (3,35), (3,67), (8,9), (8,72), (10,11), (10,42), (10,74), (32,33), (32,34), (32,96), (40,41), (40,42), (40,104), (64,65), (64,66), (64,72), (64,96)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_107.map (· &&& dom_107)
def goalM : Nat := goal_107 &&& dom_107
def NN : Nat → Nat
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|6,0=>0xde658
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f00000f0f0000000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f00c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x4688
|_=>0
def stOffB : Nat → Nat → Nat
|6,0=>0x5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 108 (i % 32) else 0
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
    (if pm.testBit 0 then [(dom_106,5,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 1 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 2 then [(dom_99,5,runOps true dom_99 (0,roots_99) ops)] else [])++(if pm.testBit 3 then [(dom_75,5,runOps true dom_75 (0,roots_75) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_107 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_99 _ g hchk
    · exact cpcs (by decide +kernel) low_75 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_106 5 s (0, roots_106) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_107 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_106 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_107 == dom_107) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_107 goalM v ys) : RunD true dom_107 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_107 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
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

theorem low_201_l64 : Lower true dom_201 roots_201 goal_201_l64 5 :=
  lower_slice (d:=dom_201) (dSub:=dom_137) (T:=goal_201_l64) (TSub:=goal_137) (roots:=roots_201) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000000000000000000003030000000000000000, 0, 64)] (by decide +kernel) (by decide +kernel) low_137

theorem low_233_l96 : Lower true dom_233 roots_233 goal_233_l96 6 :=
  lower_slice (d:=dom_233) (dSub:=dom_201) (T:=goal_233_l96) (TSub:=goal_201_l64) (roots:=roots_233) (rootsSub:=roots_201)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000000000003030000000000000303000000000000030300000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_201_l64

theorem lowZ_233_2_96 : Lower true dzo_233_2 roots_233 gzo_233_2_96 6 :=
  lower_iso (d1:=dom_233) (roots1:=roots_233) (T1:=goal_233_l96) [(dom_233, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_233_l96

namespace S_235
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (1,129), (2,34), (2,66), (3,11), (3,35), (3,67), (3,131), (8,9), (8,72), (8,136), (10,11), (10,42), (10,74), (10,138), (32,33), (32,34), (32,96), (32,160), (40,41), (40,42), (40,104), (40,168), (64,65), (64,66), (64,72), (64,96), (64,192), (128,129), (128,136), (128,160), (128,192), (130,131), (130,138), (130,162), (130,194)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_235.map (· &&& dom_235)
def goalM : Nat := goal_235 &&& dom_235
def NN : Nat → Nat
|5=>0x2
|6=>0x8
|7=>0x9
|8=>0x3
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0x6d63128e19
|6,0=>0xe3c93996fb79f7d791bb6fb22611255c4c05a872
|7,0=>0xf701becefb9bbec708306fc3a60b7a4388b34df703527
|8,0=>0x6a2132aab405a18
|9,0=>0xf0b1
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xe0e00000e0e00000e0e00000e0e50500000505000005050000050500000505000005050000000000000000f0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0a50500000505000005050000050500000404000004040000040400000404f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0c00f0000000f0000000f0000000f0000000f0000000f0000000a0000000af0f00000f0f000000000000000000000f0f00000f0f0000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ec0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0ca0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0af0f0000000000000f0f0000000000000f0f0000000000000f0f00000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f00f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0ef0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0a00000a0af0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x19928010664a0ad490654408332005090664a0af490654088329d090106649428690664850e2906b48083305c020d602848340921219282a8864a005510c9415aa20ce90a1a419589011690154418820
|1=>0x8490662a124194e920cc82b8a4
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x56005
|6,0=>0x3863262c62661f71871170b6
|7,0=>0x7476e66776075a65374b84473e6
|8,0=>0x8968277b7
|9,0=>0x8f6
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 17 then fld (dictB (i / 512) (i / 32 % 16)) 236 (i % 32) else 0
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
|0=>0x3154154a10154a141e3154954a10174a141d3154253150a14952a14954a13214252a14954954a132149541d31568f0154a168f0154a168f0154a10a14953154a12ae32142549541d315
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x4
|6,0=>0x64d634cd0334ca31cc43
|7,0=>0x2c2a8a8298a4288a02789c2
|8,0=>0x301bc6e1
|9,0=>0x310
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 10 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x54
|6,0=>0x13fa7e07e02c01000212223e
|7,0=>0xd3f0ffc3f80f06e0ffd2a53fa7e
|8,0=>0xff13f83f
|9,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 12 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_233,8,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 1 then [(dom_227,8,runOps true dom_227 (0,roots_227) ops)] else [])++(if pm.testBit 2 then [(dom_203,8,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 3 then [(dom_234,7,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 4 then [(dom_171,7,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 5 then [(dom_107,7,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 6 then [(dzo_233_2,6,runOps true dzo_233_2 (0,roots_233) ops)] else [])++(if pm.testBit 7 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 8 then [(dom_106,5,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 9 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 10 then [(dom_170,4,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 11 then [(dom_43,4,runOps true dom_43 (0,roots_43) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_235 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_233 _ g hchk
    · exact cpcs (by decide +kernel) low_227 _ g hchk
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_233_2_96 _ g hchk
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) low_106 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_43 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_233 8 s (0, roots_233) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_235 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_233 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_235 == dom_235) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_235 goalM v ys) : RunD true dom_235 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_235 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_235 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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

theorem low_203_l2 : Lower true dom_203 roots_203 goal_203_l2 8 :=
  lower_slice (d:=dom_203) (dSub:=dom_201) (T:=goal_203_l2) (TSub:=goal_201) (roots:=roots_203) (rootsSub:=roots_201)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c, 0, 2)] (by decide +kernel) (by decide +kernel) low_201

theorem lowZ_203_16_2 : Lower true dzo_203_16 roots_203 gzo_203_16_2 8 :=
  lower_iso (d1:=dom_203) (roots1:=roots_203) (T1:=goal_203_l2) [(dom_203, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_203_l2

theorem low_202_l2 : Lower true dom_202 roots_202 goal_202_l2 5 :=
  lower_slice (d:=dom_202) (dSub:=dom_200) (T:=goal_202_l2) (TSub:=goal_200) (roots:=roots_202) (rootsSub:=roots_200)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x404000000000000040400000000000004040000000000000404, 0, 2)] (by decide +kernel) (by decide +kernel) low_200

theorem lowZ_202_16_2 : Lower true dzo_202_16 roots_202 gzo_202_16_2 5 :=
  lower_iso (d1:=dom_202) (roots1:=roots_202) (T1:=goal_202_l2) [(dom_202, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_202_l2

namespace S_90
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (8,72), (10,26), (10,74), (16,18), (24,26), (24,88), (64,66), (64,72), (80,82), (80,88)]
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

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

namespace S_218
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (8,72), (8,136), (10,26), (10,74), (10,138), (16,18), (24,26), (24,88), (24,152), (64,66), (64,72), (64,192), (80,82), (80,88), (80,208), (128,136), (128,192), (130,138), (130,146), (130,194), (144,146), (144,152), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_218.map (· &&& dom_218)
def goalM : Nat := goal_218 &&& dom_218
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x4dd4f0ca1a
|5,0=>0x46ab0232ba0304e
|6,0=>0x33489
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x28282828000000002828282800000000280028000000000028002805050505000000000500050000000000050505050000000005000500a0a0a0a000000000a0a0a0a0000000000000000000000000000000000000000000000000000000000000001414141400000000000000028282828000000002800280000000000000000000000000000000005050000000000000505000000000000050500000000000005050000808080800000000080808080000000008080808000000000808080941414140000000000000000000000001414141400000000000000028002800000000002800280000000000280028000000000028002800000000000000000000000000000000050505050000000005000500
|_,_=>0
def stPool : Nat → Nat
|0=>0x724132437197432181432764321543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 219 (i % 32) else 0
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
|0=>0x1c52149f
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
|5,0=>0x2113
|6,0=>0x1e
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_202,5,runOps true dom_202 (0,roots_202) ops)] else [])++(if pm.testBit 1 then [(dzo_202_16,5,runOps true dzo_202_16 (0,roots_202) ops)] else [])++(if pm.testBit 2 then [(dom_200,4,runOps true dom_200 (0,roots_200) ops)] else [])++(if pm.testBit 3 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 4 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_218 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_202 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_202_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_200 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_90 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_202 5 s (0, roots_202) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_218 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_202 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_218 == dom_218) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_218 goalM v ys) : RunD true dom_218 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_218 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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

theorem low_75_l2 : Lower true dom_75 roots_75 goal_75_l2 5 :=
  lower_slice (d:=dom_75) (dSub:=dom_73) (T:=goal_75_l2) (TSub:=goal_73) (roots:=roots_75) (rootsSub:=roots_73)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c, 0, 2)] (by decide +kernel) (by decide +kernel) low_73

theorem lowZ_75_16_2 : Lower true dzo_75_16 roots_75 gzo_75_16_2 5 :=
  lower_iso (d1:=dom_75) (roots1:=roots_75) (T1:=goal_75_l2) [(dom_75, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_75_l2

namespace S_91
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,18), (2,66), (3,11), (3,19), (3,67), (8,9), (8,72), (10,11), (10,26), (10,74), (16,18), (17,19), (17,25), (17,81), (24,25), (24,26), (24,88), (64,65), (64,66), (64,72), (80,81), (80,82), (80,88)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_91.map (· &&& dom_91)
def goalM : Nat := goal_91 &&& dom_91
def NN : Nat → Nat
|4=>0x2
|5=>0x3
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x462f83dd0c
|5,0=>0xad6c826e500ef3f
|6,0=>0x3f37a
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0a0f0a000000000f0a0f0af0f0f0f000000000f000f0050505050000000000000000a0a0a0a000000000a0a0a0a00f000f00000000000a000af0f0000000000000f0f0000c0c0c0c000000000c0c0c0cf0f0f0f0000000000000000f000f00000000000f000f00a0a0a0a000000000a000a00
|_,_=>0
def stPool : Nat → Nat
|0=>0x241362431694632184132674326543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa05
|5,0=>0x59a0ca6
|6,0=>0x1c5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 10 then fld (dictB (i / 512) (i / 32 % 16)) 92 (i % 32) else 0
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
|0=>0x592149b
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
|5,0=>0x1207
|6,0=>0x1e
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 5 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_75,5,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 1 then [(dzo_75_16,5,runOps true dzo_75_16 (0,roots_75) ops)] else [])++(if pm.testBit 2 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 3 then [(dom_73,4,runOps true dom_73 (0,roots_73) ops)] else [])++(if pm.testBit 4 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_91 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_75 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_75_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_90 _ g hchk
    · exact cpcs (by decide +kernel) low_73 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_75 5 s (0, roots_75) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_75 h

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

theorem low_91 : Lower true dom_91 roots_91 goal_91 7 := S_91.noCircuit

theorem low_153_l16 : Lower true dom_153 roots_153 goal_153_l16 5 :=
  lower_slice (d:=dom_153) (dSub:=dom_137) (T:=goal_153_l16) (TSub:=goal_137) (roots:=roots_153) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000000000000000000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_137

theorem lowZ_153_2_16 : Lower true dzo_153_2 roots_153 gzo_153_2_16 5 :=
  lower_iso (d1:=dom_153) (roots1:=roots_153) (T1:=goal_153_l16) [(dom_153, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_153_l16

theorem low_155 : Lower true dom_155 roots_155 goal_155 6 :=
  lower_slice (d:=dom_155) (dSub:=dzo_153_2) (T:=goal_155) (TSub:=gzo_153_2_16) (roots:=roots_155) (rootsSub:=roots_153)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0000000000000000000000000c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) lowZ_153_2_16

namespace S_219
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (1,129), (2,18), (2,66), (3,11), (3,19), (3,67), (3,131), (8,9), (8,72), (8,136), (10,11), (10,26), (10,74), (10,138), (16,18), (17,19), (17,25), (17,81), (17,145), (24,25), (24,26), (24,88), (24,152), (64,65), (64,66), (64,72), (64,192), (80,81), (80,82), (80,88), (80,208), (128,129), (128,136), (128,192), (130,131), (130,138), (130,146), (130,194), (144,145), (144,146), (144,152), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
|4=>0x3
|5=>0x18
|6=>0x37
|7=>0x14
|8=>0x3
|9=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x64fd21b1e50e01e
|5,0=>0xe0dab80a006449e626ca536885105a4e53e43beb3f0b33488d2b3b72615f208221b1e518e5a186bd1862e14f690fc6d0c2b50ab1308f1402d9901d5b
|6,0=>0xf110fc2424bad3bb7520a924aa84ad80c946fb1e6cd6969a8f67e7c6449e60b0b5fc7e5820b54a344fb0c4c2334bf404a6b7446b843beb40da13ef2c3e1d4335e2304fc2c8c92c61529fe926b6c25c642109e208ce1c40f1796b175b3139a1135b311238104ed1021c101e20f1de0dd420d2730c2b50bcd20904408077070620472e039850310302a7e
|7,0=>0xb651e9299e8b890827046bb91639494701f3eca23e529304202f643214fe1d97017b97143320dd420bf6f07ef003faa01f13
|8,0=>0xd07566534545937
|9,0=>0x6f0dd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f000000000f0f0f0f0000000005050505000000000000000050505050000000005050505000000000500050000000000050005000000000000000000f0f0f0f00000000050505050000000000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a0000000000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a000a00f0f0f0f0000000000000000000000000f000f0000000000000000000000000000000000f0a0f0a0000000000000000000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f000f00000000000f000f00f0f0f0f000000000e0e0e0e000000000f0c0f0c000000000e0c0e0cf0f0f0f0000000005050505000000000f0f0f0f00000000050005005050505000000000000000000000000050505050000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f000f00a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af000f00000000000f000f00000000000f000f00000000000a000a00f0f0f0f0000000000000000000000000f0f0f0f0000000000000000505050500000000050505050000000005050505000000000000000000000000000000000000000000000000f0f0f0f000000000a0a0a0af0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0af000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000f000f00000000000f0a0f0a000000000f000f0000000000000000000000000000000000f0f0f0f000000000f000f00f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0aa0a0a0a000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a00000000000000000000000000000000f0a0f0a000000000f0a0f0af0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00f0f0f0f000000000a0a0a0a000000000f0a0f0a000000000a0a0a0af0f0000000000000f0f0000000000000f0f0000000000000f0f0000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000f0f0f0f000000000a0a0a0a000000000f000f00000000000a000a00f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a
|0,1=>0xa0a0a0a00000000000a000a000000000a0a0a0a0000000000000000f0f0f0f0000000000000000000000000f0a0f0af0a0f0a000000000f0a0f0a000000000f0f0f0f000000000f0a0f0af0f0f0f000000000f0a0f0a00000000000000000000000000000000f000f000000000000000000000000000f050f0500000000000000000000000000000000505050500000000000000000000000005000500f000f00000000000f0f0f0f000000000f000f00000000000f0a0f0a0000000000000000000000000000000000500050000000000000000f0f0f0f000000000c0c0c0c000000000e0e0e0e000000000c0c0c0c0000000000000000f0f0f0f0000000000000000000000000a0a0a0af0f0f0f0000000000000000000000000a0a0a0a0000000000000000f0f0f0f000000000f0f0f0f0000000000050005000000000000000000f000f000000000000000000000000000f000f0000000000000000f0a0f0a0000000000000000000000000f0a0f0a000000000000000000f000f00000000000f000f00000000000f000f00000000000a000a0000000000000000000000000000000000f000f00000000000a000a005000500000000000000000000000000050005000000000000000000000000000000000000000000000000505050500000000000000005050505000000000500050000000000050505050000000005000500f0f0f0f000000000f0f0f0f000000000505050500000000050005005050505000000000505050500000000050505050000000005000500500050000000000050005000000000005050505000000000500050000f000f00000000000f000f00000000000f000f0000000000000000f0f0f0f000000000f0a0f0a000000000f0f0f0f000000000f0a0f0a00f000f00000000000a000a00000000000f000f00000000000a000af0f0f0f000000000c0c0c0c000000000f0e0f0e000000000c0c0c0c00f000f00000000000f000f00000000000a000a00000000000a000a00000000000000000000000000000000f0f0f0f000000000f0a0f0af0f0f0f000000000f0f0f0f000000000f0a0f0a000000000f0a0f0af0f0f0f0000000000000000000000000f0a0f0a000000000000000000000000000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a
|0,2=>0xf000f0000000000000000f050f05000000000f000f00000000000f050f05000000000f000f00f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0a0f0af0a0f0a000000000f0a0f0a0000000000000000000000000f0a0f0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x80c0060e242030045018080c9910e302031a7889f080c6822a78684064c11d080c68a0e702031a44d8b080c3860a1019132607040600887021038d224cb84061c6962a1018e1a50504061c99124342032240784063810600101871434604060038b141018612202030e182840608080
|1=>0x1410187264468c084c1911a08584064c0110e2c384063499150101871a608ab080c3932248203221c69354109830e09486080c698224cf84064c8860e20203223438636101871c446a8080c69322a1207080c011149c2071a4c8a6080c10d4a282031a4c8a4080c682148c2031a283a2
|2=>0x1a4c88768101871a78895080c9871e3598406349910e702032600307421c2032619904064498714c42031a4d68704101871a449ab080c38d224d804061c691286c2031a4d40742101871a4c896080c6935e1c10d080c98e227c2031a183931210180221838e080c88d261d607080c006
|3=>0x268068622101981c002030e349917c1018d26443bd080c6930045e04063488a0e8c2030e4c6917610187301898a080c69322902030e3499144101871a449ba080c3932235c84061c69322e06840638111141c20326008a71a1039322dc684061c8a0201019322d8698080c3932230203
|4=>0x26101871a608c31a1018726457041a0c8872608804260c6860e0820d064c5072208213061c10d661c203260088622101871a609a3084c1910e35487080c69322a0384064498d84101871a608932a10383223498650101871a60893141018d26443c1080c693221e004061c6917e10187
|5=>0x391083419326442030e34c07084c1911a18684260c88742442030e349a30e1018d26008a826101871a44d11080c38d26788840634c131c1c2031a4c899
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xa50154005
|5,0=>0x2618926231886620187a61d186e61a18626171856614184b511583f60e583360b5827608581b605580f6
|6,0=>0x2107825e0367f1df667bdde87785dda774ddcc77199bf76e1db176a9da37671d96663dd88760997b75d1d6d7599d5f7565952752dd4474f5d3674bdd287485d1a744dd0c7415cff63e1cf173a9ce37371cd6633dcc87305cba72cdcac7295c9e7
|7,0=>0xa91e9c8a55e8e7a1de8079e227179a6262796a2537931e4488f5e3678bde27887e2178
|8,0=>0x2b97ac9eab7
|9,0=>0x2c06
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 68 then fld (dictB (i / 512) (i / 32 % 16)) 220 (i % 32) else 0
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
|0=>0x224d22352635281f1a09221d0e1a22352635265230450e351a801c450e4d22351a0a221d0e55224f1a1d0e022235263526500e1922351a29224d0e4d0ea200451a4d1437224d1a4d440d4644304d0e3526850e46223526351a1d0e29224d1a4d00080e45224d1a4d2669226022350e3530280e35224d1a4d26451a09221d261d
|1=>0x1a4d22971c370e4d0ea200451a4d4644304d0e354646304d0e35224d221d261d5037004526356a0d1c440e4d404f1c450e4d1a1d1c47261d6a351c440e4d0008221d1a4d0e46223526352200223526351a820e29224d221d261a2235302a224d0e350e4600451a4d221d00461a4d0eb91c46261d26850e4622350eb5261a2235
|2=>0xe352235221f304d0e3500451a4d30440e35304f0e350e4d1a1d00471a4d30460e351c460e4d260a221d0e4522350e45224d1a46221d22352635304d0e351a0a221d00451a4d1a55224f224f0e3526192235224d0e350087221f1a4d344e30440e351a451c450e4d1a4d0e4d1a1d4647304d0e350ea00045
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x1840000000000001441040000000000000c4000084000044000000004000000000000000
|6,0=>0x8e38b38838538230007f30007c30007937630000007337036d36a36736436130000000005e35b35835535230004f30004c30004934634330004033d30003a33730003433130002e32b32832532231f31c3
|7,0=>0xb72b52b32b12af2ad2ab2a92a72a52a32a129f29d29b2992972952932912
|8,0=>0xbb1ba1b91
|9,0=>0xbc0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 16 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 12 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|5,0=>0x8000000000010040000000000004000030001400000010000000000000
|6,0=>0x800304037008000100004c0000c0a0000000c67214434041019c00000000fc4014c0408000040000800008045040000805c00021010000401300050040800c02008014
|7,0=>0xef8c41fa0ecdcaa94c7e1907819e7837b940f8be1f47725034
|8,0=>0x23e1f87e
|9,0=>0x3e
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 10 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_203,8,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 1 then [(dzo_203_16,8,runOps true dzo_203_16 (0,roots_203) ops)] else [])++(if pm.testBit 2 then [(dom_218,7,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 3 then [(dom_201,7,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 4 then [(dom_211,7,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 5 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 6 then [(dom_155,6,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 7 then [(dom_210,4,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 8 then [(dom_90,4,runOps true dom_90 (0,roots_90) ops)] else [])++(if pm.testBit 9 then [(dom_83,4,runOps true dom_83 (0,roots_83) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_219 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_203 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_203_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_218 _ g hchk
    · exact cpcs (by decide +kernel) low_201 _ g hchk
    · exact cpcs (by decide +kernel) low_211 _ g hchk
    · exact cpcs (by decide +kernel) low_91 _ g hchk
    · exact cpcs (by decide +kernel) low_155 _ g hchk
    · exact cpcs (by decide +kernel) low_210 _ g hchk
    · exact cpcs (by decide +kernel) low_90 _ g hchk
    · exact cpcs (by decide +kernel) low_83 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_203 8 s (0, roots_203) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_203 h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_219 == dom_219) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_219 goalM v ys) : RunD true dom_219 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_36 : ∀ i, 36 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_48 : ∀ i, 48 ≤ i → i < 55 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 48 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 55 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_12 : ∀ i, 12 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 12 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := (range_split z7_0 z7_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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

theorem low_219 : Lower true dom_219 roots_219 goal_219 10 := S_219.noCircuit

theorem low_234_l2 : Lower true dom_234 roots_234 goal_234_l2 6 :=
  lower_slice (d:=dom_234) (dSub:=dom_232) (T:=goal_234_l2) (TSub:=goal_232) (roots:=roots_234) (rootsSub:=roots_232)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x40400000404000004040000040400000404000004040000040400000404, 0, 2)] (by decide +kernel) (by decide +kernel) low_232

theorem lowZ_234_16_2 : Lower true dzo_234_16 roots_234 gzo_234_16_2 6 :=
  lower_iso (d1:=dom_234) (roots1:=roots_234) (T1:=goal_234_l2) [(dom_234, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_234_l2

theorem low_122 : Lower true dom_122 roots_122 goal_122 6 :=
  lower_slice (d:=dom_122) (dSub:=dom_114) (T:=goal_122) (TSub:=goal_114) (roots:=roots_122) (rootsSub:=roots_114)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5000500050005000500050005000500, 64, 72)] (by decide +kernel) (by decide +kernel) low_114

theorem low_186 : Lower true dom_186 roots_186 goal_186 5 :=
  lower_slice (d:=dom_186) (dSub:=dom_178) (T:=goal_186) (TSub:=goal_178) (roots:=roots_186) (rootsSub:=roots_178)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x50005000500050000000000000000000500050005000500, 128, 136)] (by decide +kernel) (by decide +kernel) low_178

namespace S_250
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,66), (8,72), (8,136), (10,26), (10,42), (10,74), (10,138), (16,18), (24,26), (24,88), (24,152), (32,34), (32,96), (32,160), (40,42), (40,104), (40,168), (48,50), (48,112), (48,176), (56,58), (56,120), (56,184), (64,66), (64,72), (64,96), (64,192), (80,82), (80,88), (80,112), (80,208), (128,136), (128,160), (128,192), (130,138), (130,146), (130,162), (130,194), (144,146), (144,152), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_250.map (· &&& dom_250)
def goalM : Nat := goal_250 &&& dom_250
def NN : Nat → Nat
|4=>0x4
|5=>0x13
|6=>0x1a
|7=>0x7
|8=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xee6d6b9ea4b587135511
|5,0=>0xe2550e1f72e12b5db0e0c739ac0bdbb73a1b64ab9f76a8e0d48802180a3b65ad9627d52be82298cb1b99a1add709014
|6,0=>0xf6f7bf103ef07eddf2bfdecedd9136d7718bc2e2bb7b2baa68b46c1ac565ab2fa9945c985a38a63172e0f55de34809b43337319eb29c951cd480efa80d9b601917
|7,0=>0xefcd5e23b4cbf96bfeef9d0695798835302
|8,0=>0xf38e2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x80808080808080808080808080808080a0a0a0a0a0a0a0a0808080808080809414040414140404141400001414000014140404141404041414000014140000808080808080808000000000000000008080808080808080000000000000005050505050505050505050505050505010101010101010100000000000000000000a0a00000a0a00000a0a00000a0a000008080000080800000808000008094141414141414140000141400001414141414141414141400001010000010128282828282828282828282828282828202020202020202020202020202020200004040000040400000404000004040000040400000404000004040000040400008080000080800000808000008080a0a0a0a0a0a0a0a000008080000080941414141414141414140000141400001414101014141010141400001414000282828282828282828280000282800002828282828282828282800002828000005000500050005000500050005000500050005000500050000000000000000a0a00000a0a00000a0a00000a0a00000a0a02020a0a02020a0a00000a0a00000000000000000000000141400001414000000000000000000001010000010100002828000028280000282800002828000028280000282800002020000020200500050005000500050005000500050005000500050005000400040004000400000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000808080801400140014001400140014001400140004000400040004000000000000000282808082828080828280808282808082828080828280808282800002828000505050505050505000000000000000004040404040404040000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a000000000000000000010100000101000001010000010100000141400001414000010100000101282828282828282828002800280028002820282028202820280028002800280505050500000000050505050000000005050505000000000505050500000000a0a0a0a0a0a0a0a08080808080808080a0a0a0a0a0a0a0a080808080808080941414141414141414141414141414140000000000000000000000000000000282828282828282828280000282800002020202020202020202000002020000505000005050000050500000505000005050000050500000505000005050000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a0101010101010101010101010101010101010101010101010101010101010101282828282828282828282828282828282828282828282828000000000000000505050505050505050505050000000005050505040404040505050500000000
|0,1=>0x50505050505050500000000000000000404040404040404a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a08080808080808080001414000014140000101000001010000014140000141400001010000010128280000282800002828000028280000282828282828282828280000282800000000000000000000000000000000000505050505050505040404040404040400000000000000000000000000000000202020202020202000000000000000141414141414141400001010000010101414141414141414000010100000101080808080808080808080808080808080808080808080808000000000000000000000000000000000000000000000005050505050505050000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2031822c52031c66552026062d42030862d72031822d62025462d42031822d32041822c92031822d22032c21912042c21901032c218f2040c23012042c218e20318b08d2040c718c1031822c020318b08a1031c60081020492031c61440c2040
|1=>0x481031822e31880c21cb54620308754620308b88810218b05420309818b8080c25462c12040c62c284810318b09f2040c264b0481031822cc2c80c60996c62032c278620309d5481032c219c2040cb1c66480c60992d52c80c609b2031822da
|2=>0x62c81030862c80c26062040cb0871880c22d52040c218b0481030862e01881032c274b2040c60992040c608ba081032c21a71880cb0a61880cb08798810218b5080c218b9481032c21a420309818b
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x7a82940aa005
|5,0=>0x2018f4c7463731a18c4c5c62b3141894c4461f30e1864c2c6133081834c146
|6,0=>0x25af267903465e26d0d6833bfddf0ef1775b3959bced77683b25d84ebb75a3ab5d4eca164d3a4dd18e866
|7,0=>0x575aacf506a4bd09e76f347
|8,0=>0x1636
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 41 then fld (dictB (i / 512) (i / 32 % 16)) 251 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 13 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x1028b092c4462d18b8b0b182592f182461d2c247132c247132c2410f18b448118b862d102992e1824b112c24b112c24b61102810f18b462e102862d2c4410b18b428118b862d182592c182591318244752c2cb112c2c6752c2c6092c24b1118259131824b111824b09
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x30000000000000000000000000000000000000000
|6,0=>0xccb12bcad2aca920027294a32849f2749b26497254932448f2348b22487214832
|7,0=>0x3b1e8791e0771d8751
|8,0=>0x3c0
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
|5,0=>0x20000000000000000000000000000
|6,0=>0x1071ca8326004416adeb889822081236a48364024940e
|7,0=>0xffaffefdfab7
|8,0=>0x37
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 7 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_242,7,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 1 then [(dom_234,7,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 2 then [(dom_218,7,runOps true dom_218 (0,roots_218) ops)] else [])++(if pm.testBit 3 then [(dzo_234_16,6,runOps true dzo_234_16 (0,roots_234) ops)] else [])++(if pm.testBit 4 then [(dom_122,6,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 5 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 6 then [(dom_186,5,runOps true dom_186 (0,roots_186) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_250 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_242 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_218 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_234_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_122 _ g hchk
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) low_186 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_242 7 s (0, roots_242) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_250 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_242 h

def symsG : List (List (Nat × Nat)) := []
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_250 == dom_250) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_250 goalM v ys) : RunD true dom_250 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_250 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 19 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 19 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 26 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 24 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 26 → Z 6 i = true := (range_split (range_split z6_0 z6_12) z6_24)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
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

theorem low_235_l2 : Lower true dom_235 roots_235 goal_235_l2 9 :=
  lower_slice (d:=dom_235) (dSub:=dom_233) (T:=goal_235_l2) (TSub:=goal_233) (roots:=roots_235) (rootsSub:=roots_233)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c, 0, 2)] (by decide +kernel) (by decide +kernel) low_233

theorem lowZ_235_16_2 : Lower true dzo_235_16 roots_235 gzo_235_16_2 9 :=
  lower_iso (d1:=dom_235) (roots1:=roots_235) (T1:=goal_235_l2) [(dom_235, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_235_l2

theorem low_107_l2 : Lower true dom_107 roots_107 goal_107_l2 6 :=
  lower_slice (d:=dom_107) (dSub:=dom_105) (T:=goal_107_l2) (TSub:=goal_105) (roots:=roots_107) (rootsSub:=roots_105)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c, 0, 2)] (by decide +kernel) (by decide +kernel) low_105

theorem lowZ_107_16_2 : Lower true dzo_107_16 roots_107 gzo_107_16_2 6 :=
  lower_iso (d1:=dom_107) (roots1:=roots_107) (T1:=goal_107_l2) [(dom_107, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_107_l2

theorem low_59 : Lower true dom_59 roots_59 goal_59 5 :=
  lower_slice (d:=dom_59) (dSub:=dom_51) (T:=goal_59) (TSub:=goal_51) (roots:=roots_59) (rootsSub:=roots_51)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) low_51

namespace S_123
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,18), (2,34), (2,66), (3,11), (3,19), (3,35), (3,67), (8,9), (8,72), (10,11), (10,26), (10,42), (10,74), (16,18), (17,19), (17,25), (17,49), (17,81), (24,25), (24,26), (24,88), (32,33), (32,34), (32,96), (40,41), (40,42), (40,104), (48,49), (48,50), (48,112), (56,57), (56,58), (56,120), (64,65), (64,66), (64,72), (64,96), (80,81), (80,82), (80,88), (80,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_123.map (· &&& dom_123)
def goalM : Nat := goal_123 &&& dom_123
def NN : Nat → Nat
|4=>0x4
|5=>0x13
|6=>0x1a
|7=>0x7
|8=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xc32c477a726891a0bf6f
|5,0=>0xeeb14ed21aeb425b20daa1af0901217f789784fb6fad5668885a7773959e2f85016e2d1447f0ea85072af0633104ff7
|6,0=>0xd81cfbfcbda5f899bf7696ff994cdf8f5248b6678204778c2e72daa6b21f69068573be50aaf4f22a4d3134a6a143cd83671e3628c2cb351e6661e10a1a7b818575
|7,0=>0xfc06ff27efb11167e20374be35fd4c28e28
|8,0=>0x528e8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x3030303030303030202020202020202f0f0f0f0f0f0f0f00000c0c00000c0c505050505050505040404040404040410101010101010100000000000000000000000000000000e0e0e0e0e0e0e0ef0f01010f0f01010f0f00000f0f00000000c0c00000c0c00000c0c00000c0c00000000f0f0f0f000000000e0e0e0e00b000b000b000b000a000a000a000ae0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f03030f0f03030f0f02020f0f020200000000000000000000e0e00000e0e00f000f000f000f000a000a000a000af0f0f0f0f0f0f0f0f0f00000f0f0000f0f0f0f0f0f0f0f00000e0e00000e0ee0e0e0e0e0e0e0e00000000000000000000f0f00000f0f00000e0e00000e0e00f000f000f000f000e000e000e000ef0f0e0e0f0f0e0e0f0f00000f0f00000000d0d00000d0d00000c0c00000c0cf0f0f0f0f0f0f0f00000000000000005050d0d05050d0d00000c0c00000c0cc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0e0f0e0f0e0f0e0f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f000000000f0f0f0f00000000e0e0e0e0e0e0e0e0e0e00000e0e0000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0e0e0e0e0f0f0f0f00000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c
|0,1=>0xf0f03030f0f03030f0f00000f0f0000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0ef0f05050f0f05050f0f00000f0f00000000e0e00000e0e00000e0e00000e0e3030303030303030000000000000000b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a0000f0f00000f0f00000c0c00000c0c5050505050505050000000000000000d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0c
|_,_=>0
def stPool : Nat → Nat
|0=>0x18b0896531032422d81032422c11842c90971830960121832c22551840c24001832422d41842422c81890932d21832422d11840c94071832422cf1842422ce1832422c51832422cd1832c224c1832c224a1032411c61092071830801440c2040
|1=>0x4860c22402d218424b0874c60c22c90222c60c90969460c22644861032c90a318308b2621840cb0898061092c24c61032c225f1830892de1840cb2427460c90962d21830890121840c908b4060cb0872591840c908b7061032422db1832422da
|2=>0xb1840c908610324b0a12c60c22591840c22c990610324b0871840c22c90060c908b48b1840c90961840c258b0060c22c9a061032422e71832c28496460c92c298b1832429461032562c71832421cb
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x7a82940aa005
|5,0=>0x2018f4c7463731a18c4c5c62b3141894c4461f30e1864c2c6133081834c146
|6,0=>0x25af276903c65e26d0d6833bfddf0ef17753b8ddbacd67683325d86cbc75b32bdd50ea264dba51d1ae867
|7,0=>0x571eacd4f7a43d05e76d347
|8,0=>0x1636
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 41 then fld (dictB (i / 512) (i / 32 % 16)) 124 (i % 32) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 6 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 13 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x2c2c4262c9cb092c94b112424b2524244912c9cb5924244262c2c4852c2c45a2424b092424b112c24b112c9470f2c240132c9445a2424b112c9c2912c9c0132c949852c2c70f2c247272c24b651098b112424b112c94b5824244262c24b5b2424b5a2424b112c94909
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xc00000000000000000000000000000000
|6,0=>0xccb12bcad2aca929ca528ca127c9d26c9925c9524c9123c800348b22487214832
|7,0=>0x3b1e8791e0771d8751
|8,0=>0x3c0
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
|5,0=>0x100000000000000000000000
|6,0=>0x5060e613164627909642b2012c083026c01c775e24102
|7,0=>0x1bdfeddfb7faf
|8,0=>0x2f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 7 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_115,7,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 1 then [(dom_107,7,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 2 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 3 then [(dom_122,6,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 4 then [(dzo_107_16,6,runOps true dzo_107_16 (0,roots_107) ops)] else [])++(if pm.testBit 5 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 6 then [(dom_59,5,runOps true dom_59 (0,roots_59) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_123 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_115 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) low_91 _ g hchk
    · exact cpcs (by decide +kernel) low_122 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_107_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_115 7 s (0, roots_115) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_123 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_115 h

def symsG : List (List (Nat × Nat)) := []
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_123 == dom_123) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_123 goalM v ys) : RunD true dom_123 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_123 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 19 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 19 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 26 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 24 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 26 → Z 6 i = true := (range_split (range_split z6_0 z6_12) z6_24)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 7 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, bar true dom_123 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_123 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_123 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_123 roots_123 goal_123 9 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_123

theorem low_123 : Lower true dom_123 roots_123 goal_123 9 := S_123.noCircuit

theorem low_187 : Lower true dom_187 roots_187 goal_187 8 :=
  lower_slice (d:=dom_187) (dSub:=dom_179) (T:=goal_187) (TSub:=goal_179) (roots:=roots_187) (rootsSub:=roots_179)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f0000000000000000000f000f000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) low_179

theorem low_249_l112 : Lower true dom_249 roots_249 goal_249_l112 7 :=
  lower_slice (d:=dom_249) (dSub:=dom_233) (T:=goal_249_l112) (TSub:=goal_233_l96) (roots:=roots_249) (rootsSub:=roots_233)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000030300000303000003030000030300000303000003030000, 0, 16)] (by decide +kernel) (by decide +kernel) low_233_l96

theorem lowZ_249_2_112 : Lower true dzo_249_2 roots_249 gzo_249_2_112 7 :=
  lower_iso (d1:=dom_249) (roots1:=roots_249) (T1:=goal_249_l112) [(dom_249, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_249_l112

namespace S_251
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (1,129), (2,18), (2,34), (2,66), (3,11), (3,19), (3,35), (3,67), (3,131), (8,9), (8,72), (8,136), (10,11), (10,26), (10,42), (10,74), (10,138), (16,18), (17,19), (17,25), (17,49), (17,81), (17,145), (24,25), (24,26), (24,88), (24,152), (32,33), (32,34), (32,96), (32,160), (40,41), (40,42), (40,104), (40,168), (48,49), (48,50), (48,112), (48,176), (56,57), (56,58), (56,120), (56,184), (64,65), (64,66), (64,72), (64,96), (64,192), (80,81), (80,82), (80,88), (80,112), (80,208), (128,129), (128,136), (128,160), (128,192), (130,131), (130,138), (130,146), (130,162), (130,194), (144,145), (144,146), (144,152), (144,176), (144,208)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3fffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
|4=>0x2
|5=>0x16
|6=>0x6f
|7=>0x10e
|8=>0xc3
|9=>0x34
|10=>0x8
|11=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x4f74531fdb
|5,0=>0xf659dc69cec540db97618b4d07c05a77d6d548044ce9b3a9b63a7352f8782f7312cd8e2a4702714f2478b18a2f13d0712a2a0308f02f56
|6,0=>0xf4fd2ead07e8c61de86bde320db2adda955d8b2cd165ed1358cc8dccba8dc4124bee10b9d55b9234b5d37b4b2ab1054ae259ad814a4017a2b4d9dce19c10e9bffd98e9f98e4997b9c958bf945d590c308bfdf8af908aca88726b838058348d831527828f76e6b767ce767937427c73a427075d6b655698cc6934c659e862cde623c261e235d08b55351551d254bfe5480c540e451d3851b5a4f9e84f87c4ef3a4e1544d7824d0234bc0848f354842c4332b4218d408b53f4fb3d5d23cae13bbca39a423972d35f3b33e99333c9300802f93e2e7202b4812b081263da261bc25416232911fec31f6791ae2c18fae187d11616a140841368e0f43b0cbe90a4f2078e905cf00518403fe50343e0220b020f80129a00195
|7,0=>0x5218a51d385185b5121b511aa510995048f4fe124f5024f46b4d6db4d1634c4724c44e4bcd34bbbb4b8fb4b0f848c0e489ab488e7484fb48470484214824f45c5e453ea44de74483b43e1743697433b84315b42c6141beb40fa74065f3f00c3dfe83ded53adbb3a3063929c3811436ec636b2f3501234fb6347ca3388d3230330daf304bd2f93e2da182d22f2cc122cc0f2bdb32abc32a02d28e9828a2f2822627c132630c261bc2608925c4e25816254e22311a22bad221ed21fbf214de208141fc181f1ec1f0d81eeec1eee71e4bb1dd221da0f1d8731d6e51d33d1c9e11c48519d1e199be19873196c9188ab1813f17e9b1738614f6a14d391289712578123e2109d7101d2101a01019b101280e7980e2c30da690cf860c8bb0bc8e0bc3f0b85e0b6450b1c109ceb086b9074080660a051d5041fa0315002e250196e0129a
|7,1=>0xe8c61e3085e2175e0fb0e06b4e05fbde848de320dbce9daee3da526da04ed80aad79ead77ded5b10d593ed44ded43bbd258ad1358c8fc1c7800c012fbfed5bfafdbec36bdd27bc958bb239bb06cba9feb7b3eb68bab406cb1054af6beae67aadb6dad1c4aab78a98e1a807fa5b73a59a9a54e5a2393a20e0a17c8a07469eb4d9d8939a0f799ef199a8f9992797a14970d89690295e2d959c0944499434b9312290f1090c5d903808fcd18ca698c4bd8bf338b8458955f86496851a884d1284c588499182af48178c810ec7f7257f6fa7f6f47f3c47b5e67a4257854b78496779a775ec77557f75244737b27035d6f2166f06a6d8386a4fa6a4bb69cf96934c68ab366e5e6642c6492362e0262cde61d8c60cd85fff65f1375dd935d4b75ad1b5a9665a6d457ec95793b578ed570805686d54d8b54bed5431a540e452e1452bb2
|7,2=>0xfdaaefda3dfac80fa79dfa3dbf5c7ff1a7ef1651eff83efe17eeaa9ec64aec366eaba6
|8,0=>0x8178c7f2ea7bfdb7b88f7a5ac7942672eab71daa714a3706796d09e6cdfd6bb9c6af0868a4467fa366feb669a065cf465c4864cde64c0c632d65f8525ee075c3b85b9f55afc95acc45a6d45708056a6354efd5385b513a85124e4fa9f4f7174d8984d7844c7c54b49c49a6948f2948ed1482c74742245ac844e9b442e6441b841f6941de540e65404f53f8ad3c3c93bc203b13b3a8283811436d86368df3670c35012345c130871305342e9932e04b2c27f2c2052b4142a3b32a1ce2917d2844b2762d26c9126a3e25903258c623b8f2243b21d972155e2122a20eb020b6a1ee621a1d619f4919a311936918af9173ac166ad1444313e8713b95137c7137181145e112f310e8f10d231048e0f4950e3d50d8030d3a60d3180d0780be700ba630b6d20a5980a3ab09c37094bd08fd307ee60735f0501802ace00e750078600095
|8,1=>0xfe20cf9bb7f5c7ff1651eb260e517fe1c82e0ad5e01cedd698d9dddd855ed7f94d2993d2001c8fc1c400ac2024c12aec0753be838bbfe7bbeffb68bab686cb6616b35a9b3058b1cf3b0ba1af2d0af197aeb9bade9dadb82adb6caaa7caa2d0a954ba8bdda54e5a5437a2126a16b8a13b0a08709bb889a0f799df197fd29690b95d059434b9406293b4a9177f8fd668c85a8a6d689afe88fbe88c74857d1851c68490a82ec882ab1
|9,0=>0xffbebf1f58bc98fb80eeaf622af017ab274a71889a4ca92be98fa998584679ec77962a776e97764474aa9739ff6bc36661c16318c607305605650d304ffa94f7174b07b4a9bb4388241e7a3e294390c63556733a8832f7031fed2ee692c6eb23ebe215591ec441d2f31cb54150b10f8eb0f8dd0ca08090ee0741a0597f03c2e01de5
|10,0=>0xbca3aa406c5be3e4dd0f2f7d0233cf1889d1106e
|11,0=>0xcdebd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0000000000000000f0f0f0f0f0f0f0f0f000f000f000f000f0a0f0a0f0a0f0a0f000f000f000f000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000c0c00000c0cf0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0c0c0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0a0a0a0a0f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0f0e0e0e0e0f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0a0a0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0c0c0c0c0f0f0f0f0000000000f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a000000000000000000f000f000f000f0003000300030003000a000a000a000af0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0e0e0e0e0f0f0f0f0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0c0f0c0f0f0f0f0f000f00f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0e0e0e0e0f0f0f0f00000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e0000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ee0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0e0f0e0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0e0e0f0f0f0f0f0f0000
|0,1=>0xe0e0e0e0e0e0e0e05050505050505050e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f00000c0c00000c0c0f0f0f0f0f0f0f0f00000c0c00000c0cf0f0f0f0f0f0f0f0f0f03030f0f03030f0f0f0f0f0f0f0f0a0a02020a0a0202f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0050005000500050005000500050005000500050005000500000000000000000000000000000000000000000000000000f000f000f000f000a000a000a000a303030303030303030303030303030303030303030303030000000000000000f0f03030f0f03030f0f03030f0f03030f0f03030f0f03030f0f00000f0f000050505050505050505050505050505050505050505050505000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0000f0f00000f0f00000c0c00000c0c00000f0f00000f0f00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03030303030303030202020202020202f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0000f0f00000f0f00000e0e00000e0e00000f0f00000f0f00000e0e00000e0e0000000000000000a0a0a0a0a0a0a0a05050505050505050a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0f000f000f000f000f0e0f0e0f0e0f0e0f000f000f000f00f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0c0c0c0c0c0c0c0c08080808080808080000000000000000a0a0a0a0a0a0a0a01010101010101010a0a0a0a0a0a0a0a0000000000f000f00000000000f000f00000000000f000f00000000000e000e000000000000f0f0000000000000f0f0000000000000f0f0000000000000e0ef0f0f0f0e0e0e0e0f0f0f0f000000000f0f0f0f0e0e0e0e0f0f0f0f00000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e0000000000000000f0f0f0f0f0f0e0e0f0f0f0f0f0f00000f0f0f0f0f0f0e0e0f0f0f0f0f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0f0f0f0f00000000f0f0f0f0f0e0f0e0f0f0f0f0f000f000f0f0f0f0f0e0f0e0f0f0f0f0f000f0000a000a000a000a000f000f000f000f000b000b000b000b000a000a000a000a0000f0f00000f0f00000f0f00000c0c00000f0f00000e0e00000f0f00000c0c0000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0f0a0f0a0f0f0f0f0f000f00f0f0f0f0f0f0f0f0f0f0f0f00000c0c0f0f0f0f0a0a0e0e0f0f0f0f00000c0cf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000
|0,2=>0x3030303030303030303030303030303020202020202020202020202020202020000000000000000f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f03030f0f03030f0f0f0f0f0f0f0f0f0f02020f0f0202f0f0f0f0f0f0f0f00000e0e00000e0e0f0f0f0f0f0f0f0f00000e0e00000e0e0000000000000000f0f0f0f0f0f0f0f000000000000000000000e0e00000e0e0000000000000000f0f0f0f0f0f0f0f03030303030303030a0a0a0a0a0a0a0a50505050505050505050505050505050505050505050505040404040404040400000000000000005050505050505050303030303030303000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000a000e000a000e0000000000000000f0f0f0f0f0f0f0f00000000000000000a0a0e0e0a0a0e0e0000f0f00000f0f00000f0f00000f0f05050f0f05050f0f00000e0e00000e0e30303030303030303030303030303030303030303030303020202020202020200000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e00f000f000f000f000f000f000f000f000b000b000b000b000a000a000a000af0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f01010101010101010a0a0a0a0a0a0a0a0000f0f00000f0f00000f0f00000f0f00000e0e00000e0e00000e0e00000e0e5050505050505050505050505050505040404040404040404040404040404040000c0f00000c0f00000c0f00000c0f00000c0f00000c0f00000c0e00000c0ef0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f02020202020202020000000000000000f0f03030f0f030300000000000000000f0f02020f0f0202f0f0f0f0f0f0f0f0f000f000f000f000f0c0f0c0f0c0f0c0f000f000f000f00f0f0f0f0f0f0f0f0f0f00000f0f00000e0e0e0e0e0e0e0e0e0e00000e0e000000000000000000004040404040404040303030303030303060606060606060600f000f000f000f000f000f000f000f000f000f000f000f000e000e000e000ef0f03030f0f03030f0f03030f0f03030f0f03030f0f03030f0f02020f0f0202f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0e0e0e0e0e0e0e0e0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000d0d00000d0d0f0f0f0f0f0f0f0f00000c0c00000c0cf0f03030f0f03030f0f02020f0f02020f0f03030f0f03030f0f02020f0f0202f0f00030f0f00030f0f00030f0f00030f0f00030f0f00030f0f00020f0f0002f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000e0e00000e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c00000000000000000000f0f00000f0f000000000000000000000e0e00000e0e
|0,3=>0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0c00000000000000000000000000000000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e00000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0ea0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c0c0c00000c0c00000d0d0d0d0d0d0d0d0d0d00000d0d0000000000000000000000000000000000005050505050505050000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0b0b0b0b0b0b0b0b000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e303030303030303030303030303030301010101010101010000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050000000000000000f0f03030f0f03030f0f03030f0f03030f0f01010f0f01010f0f00000f0f0000000000000000000000000000000000005050505050505050404040404040404f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f05050505050505050404040404040404b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0af0f00000f0f00000f0f00000f0f00000f0f03030f0f03030f0f02020f0f0202000000000000000030303030303030300000000000000000202020202020202f0f00000f0f00000f0f03030f0f03030f0f00000f0f00000f0f02020f0f0202a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f08080808080808080c0c0c0c0c0c0c0c5050505050505050000000000000000050505050505050500000000000000000000a0a00000a0a00000f0f00000f0f000008080000080800000c0c00000c0c000000000000000000000000000000003030303030303030202020202020202f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0000f0f00000f0f00000c0c00000c0c00000e0e00000e0e00000c0c00000c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e3030303030303030202020202020202030303030303030302020202020202020000000000000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0ac0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0e0e0e0e0e0e0e0e00000000c0f0c0f000000000c0f0c0f000000000c0f0c0f000000000c0e0c0e00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0e0e0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000e0e00000e0e
|0,4=>0xf0f0f0f0f0f0f0f00000c0c00000c0c0a0a0e0e0a0a0e0e00000c0c00000c0c0000c0c00000c0c00000c0c00000c0c00000d0d00000d0d00000c0c00000c0cf0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000c0c00000c0c5050f0f05050f0f00000f0f00000f0f05050d0d05050d0d00000c0c00000c0cf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e0000f0f00000f0f00000f0f00000f0f00000c0c00000c0c00000c0c00000c0c1010101010101010a0a0a0a0a0a0a0a01010101010101010a0a0a0a0a0a0a0a000000000000000000000000000000001010101010101010000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f01010101010101010000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0000c0c00000c0c00000c0c00000c0c00000f0f00000f0f00000e0e00000e0ea0a0a0a0a0a0a0a00000000000000000b0b0b0b0b0b0b0b0000000000000000f0f0a0a0f0f0a0a0f0f00000f0f00000f0f0b0b0f0f0b0b0f0f00000f0f0000a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0e0e0e0e0e0e0e0e0000a0a00000a0a00000f0f00000f0f00000a0a00000a0a00000e0e00000e0e00000000000000000000000000000000f0f0f0f0f0f0f0f0a0a0e0e0a0a0e0ef0f0f0f0f0f0f0f0f0f00000f0f00000c0c0c0c0c0c0c0c0c0c00000c0c0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0c0000f0f00000f0f00000f0f00000f0f00000d0d00000d0d00000c0c00000c0cc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0e0c0e0c0e0c0e0000c0c00000c0c00000c0c00000c0c05050d0d05050d0d00000c0c00000c0c303030303030303000000000000000003030303030303030000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a0000e0e00000e0e00000e0e00000e0e00000f0f00000f0f00000e0e00000e0e00000000000000000000000000000000f0f0f0f0f0f0f0f00000e0e00000e0e101010101010101010101010101010101010101010101010000000000000000f0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f04040404040404040000000000000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0ef0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0e0030003000300030003000300030003000300030003000300020002000200020000000000000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c00000000000000000000f0f00000f0f000000000000000000000c0c00000c0c
|0,5=>0xf0f03030f0f03030f0f00000f0f00000f0f03030f0f03030f0f00000f0f0000000000000000000050505050505050500000000000000000404040404040404c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f08080808080808080a0a0a0a0a0a0a0a101010101010101000000000000000001010101010101010000000000000000f0f01010f0f01010f0f00000f0f00000f0f01010f0f01010f0f00000f0f0000505050505050505040404040404040405050505050505050404040404040404202020202020202020202020202020203030303030303030202020202020202f0f0f0f0f0f0f0f00000000000000000101010101010101000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f030303030303030300000000000000005050d0d05050d0d00000c0c00000c0c05050d0d05050d0d00000c0c00000c0cf0f00000f0f00000f0f00000f0f00000f0f05050f0f05050f0f00000f0f0000f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0808080808080808c0c0c0c0c0c0c0c00000000000000000d0d0d0d0d0d0d0d0000000000000000f0f0c0c0f0f0c0c0f0f00000f0f00000f0f0d0d0f0f0d0d0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0e0e0a0a0e0ef0f03030f0f03030f0f03030f0f03030f0f02020f0f02020f0f02020f0f0202f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0e0e0f0f0e0e0f0f00000f0f0000505050505050505050505050505050501010101010101010000000000000000f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0e0e0a0a0e0ef0f00000f0f00000f0f00000f0f00000f0f01010f0f01010f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000c0c00000c0cf0f0f0f0f0f0f0f0a0a0e0e0a0a0e0e0f0f0f0f0f0f0f0f0a0a0e0e0a0a0e0e0000d0d00000d0d00000d0d00000d0d00000d0d00000d0d00000c0c00000c0c0000000000000000f0f0f0f0f0f0f0f05050505050505050000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0eb0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a0b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a0000e0e00000e0e00000e0e00000e0e0f0f0f0f0f0f0f0f00000e0e00000e0e0000c0c00000c0c00000f0f00000f0f00000c0c00000c0c00000e0e00000e0ef0e0f0e0f0e0f0e0f000f000f000f000f0e0f0e0f0e0f0e0f000f000f000f00000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000f0f03030f0f030300000000000000000a0a02020a0a0202
|0,6=>0xf0f05050f0f05050f0f00000f0f00000f0f05050f0f05050f0f00000f0f00000000000000000000000000000000000030303030303030300000000000000001010101010101010f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000000000000000000b0b0b0b0b0b0b0b0a0a0a0a0a0a0a0af0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000000000000000000c0c0c0c0c0c0c0c04040404040404040c0c0c0c0c0c0c0cd0d0d0d0d0d0d0d0c0c0c0c0c0c0c0c0d0d0d0d0d0d0d0d0c0c0c0c0c0c0c0c0000d0d00000d0d00000c0c00000c0c00000d0d00000d0d00000c0c00000c0cf0f0e0e0f0f0e0e0f0f00000f0f00000f0f0e0e0f0f0e0e0f0f00000f0f0000f0f0f0f0f0f0f0f0f0f00000f0f00000f0f0a0a0f0f0a0a0f0f00000f0f0000e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e
|_,_=>0
def stPool : Nat → Nat
|0=>0x60407032d2c04030227290e03020428270a0e061003260c0310061d190c05041906250e0605040d011003062419220a0e0623051306100322150e0403020d010c05040619210a0c20051f1b0a0310061e1d0306100f1a0c10030616150c0605040d000e06141003130a0e060310120e060311100f06050401000403020100
|1=>0x2f200a100306241e040e03022b270a0e06073c3b3a0a0c082007042f0a0e061003300a07040306131d0a0c10170506320a0c05171006380a0e06073736130a0304070613350a0c03043402200a0c04180506320a0c04053106240a0e10031706300a0e0c102f080a0403062407130a0e0c0604052e0c0403020d000604030701
|2=>0xa0703040647130a0e0c061005460a0c04030607450a030406073e13040e06052b270a0703040644130e0c04020314110a0703040613430a0c06040307420c05040624190e0c062b05043c0c06100319150e0c03100641190a0c06040307400a0e0c0405063f0a0c0403063e3d0e0603070428270a0c05040209200a0c040203
|3=>0x402141a0c0403070616150a0c04030706470a0e0c0605230a0c0403064d4c0a0e061c1003130a0c08200504410a0e064b03103c0406030727290a0e0c051002090e0c0403063c0d0a0c040317024a0a0e0c02032f100a0e0c05101f1b0a0e0c040703490a0e0c10072f080a0e0c051706230a0604200703480a0e0c0646103c
|4=>0x73b3a0e0c050417060d0a0c06200510090e0c0403020d0a0c0304540220040306240719220a0e040506331e0a0c062010032f0e06040703532d0604030722150a0c07373606240a0e04030607480e0c040317020d0a0e04030607520a0e0c060504510a0403065007130a0c0403024a0a0c02034f10200a07030406134e030c
|5=>0xa0c082005101b030c0610141a0c0403060719210a0c06035c045b0e0c05041906160a0e0c10032f330a0e0c0610035a0a0c05171006350a0e0c070454590c06040703532c0a0e0c060310580e0c0605040d0a0e0403063c300e0c06031411100c060403070d000a040306073e570a0c0403063e560a0c04030607550a0e0617
|6=>0x1706500a0c04030263200e0c04030607530e0703040613620a0c030406074c0c040306073e610a0304060213200a0e0c0304545e0e0703040613530a0c04030607600a0c051710063e0c0403071906250e060403070d010c0604200703530a0703040613600a0c0510065f200a0c0604035e420e06050419220a0c040306075d
|7=>0x60304051307200a0c0705361706240a0e0c050417065e0e0c060403070d0a0e0c10170506650a0c0304065407200a0e0c06100305690a0c05041706073e0a0e0c07171006590a0c04030768670a0e0c060507041f0a0c041b200703330a0e0c04170607590a0c0704170506440a0c0308020410200a0703040624130a0c0510
|8=>0x101b0a0e06041707133b0a0c07030406730e0c0403071906160a0c0403170607400a0c0703043c06320a0c06032007041f0a0e0c03070617710a0c0406037007200a0c06040703056f0a0c0704033c06380a0c040307066d0a0c1003170706350a0c0305040706380a0603043c1307200a0e0c06170737360a0c060407036a0a
|9=>0x200504100a0e0c060737360a0e0c1b020305100a0c040317060742030a0c043902200a0e0703040654130a0c0304360602200a0e0c061003052f0a0c04033706073e0a0c0406241707370a0e061b071003130a0c0410030665200a0e0c06070310770a0c07031710061d0a0e0c08070504540a0e0c02047607050a0e0c080507
|10=>0x50a0e0c08056504100a0e0c070405067f0a0c03047d0506320a0c06040307400e0c060307042b280a0c0302047607200a0e0c06037e07100a0c1b20071003080a0e0c050710065f0a0c0403065007790a0c06087c07047b0a0e0c04180506330a0c040306077a0a0e0c04030907780a0c06051710200e0c061003190a0c0608
|11=>0x4030706540a0c0403067f07200a0c0603075c04870a0e0c07030454330a0e0c1b100703330a0c0705041706500a0c1003065f07200a0c06040307420a0e0c06070504860a0c0604200307850a0c0603200704830a0e0703040613820e0604030719220a0e0c1017050633030e0c0614100a0c0306241707740a0c0604800703
|12=>0xa0e0c062a05043c0a0c0620070504760a0e07030406138c0a0c0403170706470a0e0c060423050a0c0703064404340a0c04032407680a0c04030617078b0a0e0403170607300a0e0c0807042f0a0c0603200704860a0e0403070689520a0c0603203304100a0e060403073c130a0c070403067b880a0e0c03060907740a0e0c
|13=>0x607970a0e0607040537130a0c0703040696950a0c06040307930a0c0604070392910a0c0304360706350a0e06070310133a0a0c0607033e04900a0e0c05041006590a0c0703103606240a0e0c060304105e0a0c0704031006470a0c04078f03080a0c0403170902200a0e0c04810705080a0e0304070602130a0c060407038d
|14=>0x2b290a0c07030406470a0e0c06103705360a0c0703043c06600a0c0420078103080a0e0c0623050a0e0403070617520a0c0305041006350a0c0604070305600a0c0402034f200a0c040306078b0a0c06087c05047d0a0e0c030405069b0a0e06040307300a0e060704373c130a0c061b9a100305040a0e0c0605990a0e0c0317
|15=>0xc0410370506240a0e0c0307041f410a0c06040703910a0e0c07044103700a0c04031707069e0a0e0603070410480a0e0c06038307100a0c03050410061d030a0c0604079d0a0e0403170607480a0c0403064d07200a0c06041b07039c0a0e0c06040307850a0c04030209200a04030624071e0a0e0c0403020763040c060307
|16=>0xc0403070663a3030a0c1b0210200a0c03043c060220040a0e06a2050a0c040307069e0a0e0c03043407020a0e0c08050410410a0c06042003075e0e0c0703043c06530a0c0603200704a10a0e06040703480e0c0604070305530c0604030719150a0c040306073ea00a0c040306074d5d0a0c040306079f0a0e04030706520a
|17=>0x320a0e0c040203072f0a0c03050410063e0a0e0c06080536100a07030406243c130a0e0c040306074d0a070304050624130a0e070603a504520a0c0403200706630a0c07030406950a0c0410030506440a060403201707130a0c06030407a40a0e0c0403060b3c0a0e0703040665130a0e0c06070405460a0e0c07030466540a
|18=>0x30637a80a0c0403020907200a0e0c07043c0659030a0c04028f0a0c05171006240a0e0c060403075e0a0e0605041e0a0e0c040317020b0a0e0c05101706090a0c060407036f0a0c0403060264200a060304130720040e0c03022b0a0e0c060310a70a0c05041806240a0e0c05040702090a0e0c06030410a60a0c0603040710
|19=>0x3b0a0c0504170602200a0e0c08070504340a0c0403170607ab0c0403062407190a0e0c04030607890a0e0c0403020b0a0e0c060510090a0c0604200703590a0e0c0607373c360a0c03043c0706350a0e0c0610032f0a0c04030624073c0a0c04030706a30a0c060704aa03a90a0e0c04030907540a0e0703040633130a0c0704
|20=>0x3170607600a0e0c0605040b0a0c0704031006a80a0e0c080704052f0a0c0703043606320a0c0703040654470a0c0403060764350a0e0604170737130a0e0c07031706230a0e06040307130a0c0620070504090a0c040306075d0a0c07043c3706240a0e0c050417060b0a0c0604079d03ac040e0603072b270a0e0607043c13
|21=>0xa0e0c0410067f050a0c0403170607ae0a0c06049d0703050a0e0703040666130a0e0c0805101b0a0e0c05171006020e0c0403170607530a0e0c03043c065e0a0c0703043c06470a0c0517071006240a0c0403066e07200a0c03043c06073e0a0c06040703600a0e0c060703230a0c0604200703660a0e0c07050604ad0a0c04
|22=>0xa0e0c040307680a0c060407034a0a0e0c04030607660a0c04030607b10a040306241707130a0c0403063e07640a0c060403075e400a0c06040307ae0a0e0703043c06480e0c06040703530a0e0c0510065f0a0e0c06050710090a0c040306073eb00a0e0c03045407020a0c04031706074a0a0c04030706670a0c040306074c
|23=>0xe060403071e030a0c061b200710030a0e0604074b0a0e0c0305041006410a0e0c0710031706090a0e0c04030706b3040a0c0305063307200a0c040306240718030a0e0c07044139040a0c070306b50a0e0c061b071003370a0e0403060907130a0e0c0403065e790a0c04030650073c0a0c0403060907b40e0c04031706070d
|24=>0x706030471030a0c04100706350a0e0c0703043c0665040a0c07030506320a0e0c07040306b90a0e0c0305041006390a0c06041b9a07036b030a0e0c04021c040a0c03080220030a0c061b9a07100a0e0c06030407b8040a0c07030665440a0c0403170706350a0e0c03080704b70a0c0710031706240a0e0c070604b603890a
|25=>0xa0c041b07200308040e0c0603072b0a0c040317060207200a0e0c070504065f0a0e0c0703040506960a0c070304053c06240a0c060403103c07200a0e0c0607100309040a0c060307bb0a0e0c06041037050a0e0c06080705043c0a0c0604032017073c0a0e0c080705041b0a0e0c060710034f0a0e0c0504170706020a0e0c
|26=>0x103c130a0c0403065f07200a0e0c07040306377f030a0c0604078f0a0c0703047406240a0e0c0704031006540a0e0c0403370706020a0c06049a0307050a0e06040317073c13030a0c0604071d0a0e0c04031706070b0a0c0603043c07200a0e0c0403170706540a0e0c04170706a5030a0c07041006411d0a0e0c060307047e
|27=>0xa0c04031706073e0a0e0c060307041f070a0c040306af040a0e0c036507020a0e0c07040603700a0e060703043c130a0e0c060403070b030a0c06042007810a0e0607030405130a0e0c07030406540a0c030607043eaa0a0e0c0703043c06330a0e0c06030704101f0a0e0c0704100603700a0e0c041b0703330a0e06070403
|28=>0xe0c06030704970a0c030504100624040a0c070306440a0e0c060517100a0e0c06080504100a0e0c0704060339700a0e0c060407036c0a0e0c0704170506650a0e0c060407030569030a0c041006073e0a0e0c03047d0506330a0c0703043606240a0e0c04030706bd0a0c0604032007640a0e0c06050418040a0e0c08020705
|29=>0x1b0710390a0e0c070403067f0a0e0c0305040706390a0c0605041707200e0c06040307190a0e0c041b02030705030a0c0604079d0a0e0c06040307850a0e0c06030704830a0e0c0604410307050a0e0c060417073c370a0e0c0604070305be0a0e0c061b0703740a0e0c03070204760a0e0c060403073c040a0c03080207200a
|30=>0x2200a0e0c0604070305660a0c0604033707200a0e0c060417077b0a0c06040307c10a0e0c06030704c00a0e0c0603840704100a0c0403170706bf070a0c0403170650030a0e0c061c100a0e0c0704170506330a0c0603087c070410040a0c03066507200a0e0c0607043c370a0e0c06030704860a0e0c0607040537030a0e0c
|31=>0x6051707100a0e0c0608050704100a0c0403062417073c0a0c06041b20070305040a0c06032007330a0e0c0403170607980a0e0c04031706075e030a0c07041006380a0e0c040306074d0a0e0c060703103c360a0e0c0407810308040a0c060307c20a0c060307200476070a0c060403500a0e0c0703043c0666040a0c030506
|32=>0xe0c07030506047e0a0e0c0403070617720a0e0c041b0703c40a0c0703043c06240a0c040317070602350a0e0c07030406748e0a0e0c04030609073c0a0c040317068a200a0e0c060403075e0a0e0c0403070617890a0e0c06030704a10a0e0c040307c50a0e0c0305041006020a0c03050407100624040a0c070306c30a0e0c
|33=>0x6720a0c040306241707790a0e0c040317090702070a0c0403170609500a0e0c06040703460a0e0c041b070305330a0c06049a03076b0a0c0305047d06240a0e0c0403170706780a0e0c060805047d0a0e0c0403070663030a0c060407800a0e0c04030706890a0e0604031707130a0c0604031707b40a0e0c0704033706410a
|34=>0x10200a0e0c07060304c70a0e0c06041707370a0e0c060307230a0c070304053606240a0c0403062407790a0e0c06070536170a0e0c04030702090a0e0c040306090779030a0c06041b079d0a0e0c04030706780a0e06070304130a0e0c0703043c06540a0c0403062407640a0c06040307b40a0c0603080704c60a0e0c040307
|35=>0xa0c06041b0720070a0e0c04031706090a0e0c06030504100a0e0c040307066e0a0e0c0403060207640a0e0c040307680a0e0c06040703660a0c0604072003090a0e0c060307c80a0e0c04030607b20a0c0403170602200a0e0c0403170607660a0e0c03043c0706020a0c040317060907200a0e0c04030706680a0c06030504
|36=>0xc061b0710030a0e0c070604b6040a0c0306020720040a0e0c0703050633030a0e0c060407c9040a0c06030507200a0e0c06030807047d040a0c07036b0624040a0c03070635040a0e0c070306c4070a0e0c06040309040a0e0c0703050665070a0e0c0604034f030a0c070410062403070a0c06041b9a070a0c040317062403
|37=>0xa0e0c06040307640a0e0c0604031707790a0e0c060305047d030a0e0c06040781070a0e0c0403065f040a0c0306073e030a0e0c04100706020a0e0c060703043c070a0e0c041b03080a0e0c0403170706020a0e0c06070403103c0a0e0c0603050407100a0e0c06040317073c040a0e0c0603072a0a0e0c060704037b030a0e
|38=>0x2200a0e0c04070603ba0a0e0c06040307180a0e0c06041b070305040a0e0c06030733040a0c0307060235040a0c03068a200a0e0c06070403370a0c060403170720040a0e0c070306650a0e0c0607050417040a0c030706bf0a0e0c060703040536040a0e0c030807020a0e0c0604030779040a0c060703ca04070a0c06037c
|39=>0x4070a0e0c0603070a0e0c06040317040a0c06030720040a0e0c03070602040a0e0c0607030503070a0e0c06041b030a0e0c0607047d04070a0c030624040a0e0c0307068a0a0e0c04031707068a040a0c0306
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xaa0005
|5,0=>0x10ac07f603cb01d140dcc06860313017180acc050602530115407ec0396019b00b58050a022600e300598020c00a6
|6,0=>0x11cb88c9c456e224710eb8859c420c2097101387f183eae1ee70f430785c3b4e1d370e638719837ee1b870d8b86a9c346e19c70cab8639c30ee18070bcb85c9c2d6e16470af3055dc2a0e14970a1384f1826ae12f609438485c234e113708638415c1fce0f86079303adc1c8e0de606bb8341c192e0c2705db82d1c15ae0a6704fb82658124e08b7
|6,1=>0xdf5c6ece36f71b438d85c6b4e35371a638d15c67ce337719838ca5c644e31b718a38c35c60ec300717cb8bcd85d8e2e5716f38b5dc5a0e2c9716138aedc568e2ae6153b8a81c532e2927145b8a11c4fae2767137b89a584c4e25b712a38935c48ce2406
|7,0=>0x2b7c159e0ac0e55882a8415220a8105388298414a20a4105197288c1429ca08c4fc827ab93b609cb04de726b4133a098d04be825b412ba094d049e824b4123a090d047e823b411bdc8cf045f822bc113e088f043f821bc10be0850e420820c410420811040171fcc0fc607d303e271ed40f4a079503c281dd40ecdc75703a381cdc0e4e071703847
|7,1=>0x3afc1d658ea3074983a0c1ce9ce66e72b8391c1c71ce29070c8382b9bf60deb06ed837339b7a0dad06ce836341afa0d6d06ae835341a7dcd2f068f8343c1a01ccf106708334419820cb2e65183253990a0c7506337315c188e0c3706138305c180e0bf705f382f5c178e0bb705d382e5c1711cb7905b482d6416920b3ae59582c7b161e0aff05778
|7,2=>0x4a4c25061274e9328495ba495923ce9177487c241e11ff08f78477c239e11bf08d78467c231e117f08b87458422a21142e8998448c22261103087984393a1aa10c8c85d742ac2136108b083d841ac20b9d04d081f740bc203e1010e80173fcc1fc60fd4e7e283ed41f4a0f9507c283ddb9ece0f5707a383cdc1e51cf1ae78583bf39dddcedf07678
|7,3=>0x59abacb9d64d0b1e858b42c3a160eeb00757c42bc215d10ae0856cbab4615930ac1855cc2ac615530aa1854d3aa4dd5170a83853dc29d1d4d90a64852e4295214990a44851e428d5d45b0a26750f4285a141d0a0774ffc27de13df09e784f03a76213a2e9ca74e1426ea136509ab74d1c2671d329098c84c2425f212e9096c84b33257dd2af09516
|7,4=>0x17410b9885c842e2217010b7975b93adaa16c6eb5b85a9c2d2e1688eb3c8
|8,0=>0x6d8c36a61b412d9796c74b61a1afb2d7586b64b595dabb0d5496a5cb50e1a752d3376954b48a1a332d1186844b40219f10cf176744b38219af2cce9662cb2f6196cecae8652cb27259290c8c8641cb1ee18e70c6a96314316a18a32c489620bb0e9d8650c2a86114306a18250c0a8600cafe9d7e50beb75f14af6657a30bc895e042ee21762eba89
|8,1=>0x7db43eb65f4b0f9e77cb43e3ddf0d2f7e87bacbdb61ecb0f5e77ab43d365e8b0f3d879b3bcb65e492f1c878a43c321e090efc877a43bae5dc70edc7769cbb31dd890ebc8759cbaaa5d432e998748c3a261d030e798738c39a9dcc6ee5b87294b92a1c832e3897184389e5c3f0e178707c3821dc010df886f8437a5dbc30dd986e8c37261b830db98
|8,2=>0x8e4447022372f1b188d4c4682632f318e98c3445fa22ed116e88b3bc57a62ad114e88a3444f6626b112d88933c476622b110e7883443fa21eb30ec9871cc36e21a530ca8861442e6616310a988513c26a2125108a8840cc1e260df3067882fc415a609b3044981e440d220573023880e3c04e6015300377fdc3fca5fd32fe097ec43f3e5f8d2fbe8
|8,3=>0x478223af31d07
|9,0=>0x9c2ccdf9e6ed136e89b2ccd7626ab134e79a344cfa266d132e8993bcc7a662d130e8983bcc01e5f112ef9973c4b7e25af12d07963ccafe256f12ae9952cca726527328b8941c49ee24e7126b89314c96a24a512499920c48e9e465122a8910cc866242312098900c47e623e131e88
|10,0=>0x9e244ef5e76b13ad89d2c4e76272cf38e8
|11,0=>0x13cc7
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 203 then fld (dictB (i / 512) (i / 32 % 16)) 252 (i % 32) else 0
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
|0=>0xe394401b04074100d07034cc3b050645c1c040341c0d06034146c07034101d0604434390d0c42c29090706c0d06044ac392b0c4a829070801c19060346431180a4381a170700c11070446439190c46029170700c11070445039140c41c110a1c46c1c060446439190646029170700c110704434390b0a4241c080440c1d0603434390d0c42c2909070201103074180d
|1=>0x703428a908070180d031447029071b01c190604460290e0685c1c040341c0d050441c0d0a2a4201c060346439180a45c1c030441c11180a44019170700c11070441c39170641c19040341c0d070e46c14030741c190604460310e0685c1c030441c112b0c4a829070801c1906034146c060440c1d070e4180d0b0c4241c1b034101d06044cc3b050640c1d030441c11
|2=>0x71b01c1906044643919064602917070100d1f0444020070440c1d060344019070440c1d070e4180d03104101d0c1c46c1c06044ac392b0c428a908070180d170641c1904074100d070342c2917074241c17064100d092001c39070645c1904034101d1b0500c1d07064181103064146c07034101d06044402417064101d040341c0d461041c11031c46c1c06044ac31
|3=>0x1b07018110d0e42c29090706c0d06044104e03138f03317074100d040841c11030741c39060342c29090705c1907064100d070e41c193c06c1015070346431180a45c1c0e068100d180c4141917070100d07034146c07034101d070e41811190e46431180a45c1c040342c29090701c1917064100d092001c39170641c19040341c39070440c6e070641811140e47029
|4=>0x70341c39066445c1f07064100d070e4f033070641015070341c910e068101d040341c0d0d0c42c29090706c0d060441c391706c101d040341c0d190c4602917070100d070341019070440c1d070e4180d140e41c110a1c46c1c060446419180a45c1c040341c0d020ec1c1904074100d070342c2909070201103074180d0b0c45c1d090705c19040341c11031442871
|5=>0xe068100d040581c0d0907c5c19040341c0d0b0a4241c1b03418110506c0c1d030441c11070e4f01b040541c0d051bc1c0d04074181107244381a040341c0d034184019030441c11680ec601917070100d100801c1103074180d050641c0d070e418116603c241d17064100d0e654141b040341c0d070e4101d07064180d3c0cc381a040541c0d090ec5c1904074100d
|6=>0xe75419d2046b41c0f19064602917070100d0e5e8241f17064100d330ec1419040541c0d081001c11070e4180d047245c0a070640c11070e40ce51006c1c110e6946c160703418110e394401b031041c110e6e45c0b07064100d020ec1c19030441c110e394401b040741c0d070e4f033040541c0d3c04cf00f17074100d0e6c86daf0703c1811070e4f033040541c0d
|7=>0x3c04cf00f031041c11040740c1d07064181107504243b17064100d070e41c191006c1c113c0ccf01b040541c0d070e41c19040581c0d051b01c0d0407418113c03c5c1d0e068100d3c0cc400d040741811070e4141b030741c11104fc6c0f040741811410ec4019030441c113c06c141103074180d07034102207064180d040641c1103074180d03138f03317074100d
|8=>0x7044141b03074180d330ec1419040781c0d0e5e8241f1b0341811042b428a908070180d070e4102207064180d0407410ce08074180d06034101d070e418111706c101d040341c0d17078243b17064100d037d41c13080ec180d050645c1c040341c0d205fc1c391706c100d067945c1e17064100d070e4101d040341c0d180a45c1c030441c11070440c1d070e4180d
|9=>0x70e418dd031081c115c04c1df1080ec180d05064f01b040541c0d050641c0d040741811090ec5c19040341c0d070e45c1b030441c1107504243b1b03418113c08c141103074180d074f46c0f070e4181104844201f070e4180d06138f033040541c0d190c4602917070100d050640c1d030441c110704428711b0701811047945c1e0e0680c11070343a061b07c1811
|10=>0xe8e86dad0703c1811050441c0d08070180d0804c0c1d070e4180d06134f033040541c0d0e544f01b17074100d0307410a908070180d180645c1c0e068100d247945c1e0e068100d0b0c4241c17064100d1b050181103074180d081081c11070e4180d890cc5e290706c100d04074201d070e4180d3c0cc5de517078100d047945c1e170640c113c06c5de517078100d
|11=>0x7034101d1b0ec1811052ac1c0d08070180d04984241e170640c113c0ccf00f040541c0d0e96818d9040581c0d940e41d3f1b03c1811920ec0e051b07c181104138f033031041c114103c4019040741c0d0e068f013031041c116607c204107044180d0e544f01b031041c11060346c80070e41811070e41c1917064100d030641c0d1b07c18113c0cc1c19040541c0d
|12=>0x66445c1f07064100d2b0e428a908070180d0e544f01b040541c0d040580c1d031081c11660ecf019040541c0d060346c1f070e418110703410a908070180d890cc5e290706c100d020ec1c19040741c0d660ec6c15070341811070e40c6e070641811247945c1e0e068100d0704c0c1d080ec180d337dc1419040781c0d0b0c4241c1b03418113c0ccf00f031041c11
|13=>0x4d0e41d7d1706c100d182445c1c0e068100d890cc5e290706c100d0e0680c1d031081c1110064204007044180d920ec0e051b07c18110e78819e517078100d660cc204107044180d0407412110807c180d410ec4019040741c0d078043a061b07c1811660cc241d17064100d070e41d7d1706c100d6b9a41c0f1b0ec1811070e45c1907064100d180c45c1c0e068100d
|14=>0x17074241c17064100d3c0cc141b040541c0d05090201103074180d3c06cf019040541c0d0e63819911707c100d070e41c11070641811070e41c19040541c0d0307430a908070180d0e78819e517078100d100641c1103074180d0907c6c0d070e41811660acf019040541c0d0810c1c11070e4180d660cc6c15070341811660ac6c15070341811190e4602917070100d
|15=>0x1018c5c1c030441c110e0685c1c040341c0d170641c19040341c0d07a14204307044180d330ec101d08074180d1b0500c1d07064181107244381a040741c0d07044141303074180d3c0cc381a040541c0d076e45c0b07064100d3c0cc381a040541c0d066445c1f070e4100d0e96818d9040581c0d0e654141b030741c113c0cc5c1d070e4100d7d7c4101e080ec180d
|16=>0xe63819911707c100d3e03410f907244381a3c06c5c1d17064100d3c0cc1419040541c0d070e45c1907064100d6603cf019031041c11201b01c390706418110e068101d040341c0d6607c6c15070341811180c45c1c040341c0d090701c1917064100d17064101d040341c0d0e6946c16070341811070e45c1f07064100d070e4f033040541c0d2a0a41c2007064180d
|17=>0xe068f00f031041c11090705c19040341c0d9d0341e691b0ec18112b0c428a908070180d03138f033031041c11070e41c19040341c0d0e984241e17064100d180a45c1c0e068100d17984241e17064100d090705c1907064100d040841c1103074180d034186c1d070e418113c04cf00f031041c11020ec1c19040541c0d051b01c0d040741811177945c1e0e068100d
|18=>0xe068101d040341c0d070e45c0b07064100d07244381a040541c0d660ec6c15070341811100906c0d0407418111b0541c0d070e418110334811950506c1c0d660ec241d17064100d09070201103074180d0e7f818dd031081c110e544f01b040541c0d3c0ccf00f17074100d100905c19030441c113c0cc5de517078100d080440c1d070e4180d4d0e41d7d1706c100d
|19=>0x1706c101d040341c0d040841c1103074180d173e41c910e068100d07064f01b040541c0d092001c3917064100d680ec601917070100d07af8397d1706c100d0307418dd031081c110b0e4241c17064100d070341e691b0ec18113c0ccf019040541c0d040641c1103074180d07064101d040341c0d660ac241d17064100d6607cf019040541c0d0e544f01b040541c0d
|20=>0x17070381a04034401b100641c116b244381a0703c400f0407418113c0cc5c1d17064100d17074243b17064100d0e7945c1e17064100d0b0a4241c17064100db30645c0807064100d092006c0d070e41811097945c1e17064100d0eb241d7f1706c100d3c0cc5c1d0e068100d0e5e8241f1b03418110b0e4241c1b0341811660ccf019040541c0d660ac6c15070341811
|21=>0x7044141b040541c0d330ec14190703419ee037d41c131006c101d070341c0f1b0ec1811071b01c19060441c3907064180d040746c3b060441ddb0804c180d0e654141b07034083b07064100d040281c1906034381a030441c11b603412290706c603117070100d040741c390604430711b070181110064101d070345c19030441c11170201c19040341c39050641c0d
|22=>0x40541c0d3c06c5c1d040340e290706c100d410ec40190704410ce08074180d060341c390604428a908070180d070e41c19040345c1b040341c0d06364101607034381a040541c0d070e40c41070446c0d0407418110ebc4201e060340c1d031081c11050440c1d060345c1d070e4100d060440c1d060346c0f04074181107064100d0703412e9030281c19020ec1c19
|23=>0x3c0cc101507034241c1b03418111b07c1c3906044f033040541c0d3c06c10150703410f907244381a05064101507034204007044180d03394401b0704414190703418113c0cc0c41070441c391706c100d063740c42070446c80070e418110e06811ad0703cf01b031041c11070640c42070440c1d1b0ec18113c0cc5c1d04035043b1b0741811090705c19040341c39
|24=>0x603412f108078180d0e068101d0703439950506c1c0d04074100d070341c1103074180d03394401b070446daf0703c18110506c100d070346c1607034181107244381a070441419040781c0d0e0681016070345e2b0706c100d1707c1c39040345c1c040341c0d070341c19060341c910e068100d081001c1106034397d1706c100d07064141b070340ce51006c1c11
|25=>0x40341c0d07044203b060341c390506c1c0d3c03c0c4107044204207044180d3c03c101507034401b040741811063740c4207044401b040741c0d070e4100d07034602917070100d030741c19060441e691b0ec1811074f46c0f0604412110807c180d030746c1d06044f00f17074100d1b05c1c0d0604411ad0703c1811040881c19060345de517078100d070e41c19
|26=>0x80741c3906034241e17064100d0907c5c190403438e51006c1c11075f45c1b04034f013031041c11060346c1f0604438a908070180d0804c1c3906034243b1b03418113c0641015070341c39070641c0d1b0541c0d060441c39031081c11037945c1e04034603917070100d087d41c13060341c110807c180d0e8a41c1b04034243b17064100d070446c1c060441419
|27=>0x403439e517078100d100640c420704410ce050641c0d170281c190403419ad0703c18110e068101507034083b07064100d0674411ad0703c5c1d17064100d070e41c1b04034241f1b0341811178a41c1b04034204307044180d180685c1c040341c19040741c0d0e068101d070343b12066b41c0f04074100d070341c1103074180d17074381a040341c0d070e41811
|28=>0x17064100d079a46c3b0604419e517078100d3c0cc101507034f01b040541c0d1707c381a0403439e517078100d0e7d41c13060345c0a07064100d17078381a040341c1917064100d090ec5c19040340c711b0701811050641c0d060440c1e1b0ec18110e068101e0703419e517078100d0704c0c1d0603419911707c100d0e8186c1f060445e290706c100d3c0cc5c1d
|29=>0x4034101d070345c0b07064100d1707c1c1904034601917070100d1b0541c0d060446c0d070e41811042ac201c060341d7f1706c100d070e41c1904034241d17064100d070641015070341c3917064100d180645c1c040341c39040741c0da504c0e290706cf00f17074100d042a4201c06034381a040581c0d17078381a04034100d040581c0d170641c19040345c1e
|30=>0x40345c1e04034101e070346c1f060445c1b040341c910e0681c1907044101507034180d060441c19040340c4107044101d070345c1d04034201c060340df50704c101d0604412290706c1c39070641419070346c1e060441c39070341c1306034381a0703c083b0706419ad0703c6c0d06044141b070346c0f06044381a070446c3b06044381a040341c39060445c19
|31=>0x100d070e41c190703418110704c381a0706c1c1b040341c39070640c0a070645c1c040341c0d06044201d06034083b070641c390706c0c42070441c3904034141b07034100d070343a290706c1016070341c19060345c1e0403439ad0703c203b060345c1f
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>0x38000
|5,0=>0x2b60000095800000000000000000001f60000065800000000000000009b00d600ec00000000000
|6,0=>0x66280000000000063a8c2500002f545c28000166a00000000ae5152a29144fa89a512aa24140000000116a219400008150000000000000000f8a00003ba800000001c9436a86850c6a00000000000000017942ca854509ea00002528455000010141da8000000000001b2800000000c540000000
|6,1=>0x4fd49d2800000000000000135500000000000130500004ad4000000024ca000090a8000238a45d40000000224a000000010d5000000000001085206a3f947ca8000000000007a280001dea3a9472a8e051b6a35940000d15
|7,0=>0x8e111a2230445888a111222204438886110a221044188821102220043f887e10fa21f043d887a10f2200003c087710ec21d443a087310e421c4438086f10dc21b4436086b10d421a4434086710cc2194432086310c42184430085f10bc217442e085b10b4216442c085710ac215442a085310a421444
|7,1=>0x6508c91190231c46308c51188230c46108c1118022fc45f08bd117822ec45d08b9100002e040000b7116c22d445a08b3116422c445808af115c22b445608ab1154200005488a8114e229845288a41146228840000a11140227c44f089d1138226c44d08991130225c44b08951128224c44908911120223c4
|7,2=>0x82890412062408480890011fe23f847e88fc11f623e847c88f811ee23d847a880001e823cc47908f111e023bc47708ed11d823ac47508e911d0239c40000e611ca239047188e211c2238040000df11bc237446e08db11b4200006c88d811ae235846a88d411a6234840000d111a0233c46708cd1198232c4
|7,3=>0xa0093f127c24f449e093b127424e449c0937126c24d449a0933126424c4498092f125c24b4496092b125424a44940927124c200000001251000049049189221242248048f891e123a247048d891a1000046448c0917122c245448a091312242444488090f121c24344860800021624284848908120e24184
|7,4=>0x29820000a5894a129225204a38946128a25104000143128425044
|8,0=>0xbe277b8ef59de83bca7788eef9ddc3bb27758ee99dd03b9a7728ee39dc43b8276f8edd9db83b6a76c8ed79dac3b527698ed19da03b3a7668ecb9d943b227638ec59d883b0a7608ebf9d7c3af275d8eb99d703ada75a8eb39d643ac27578ead9d583aaa7548ea79d4c3a927518ea19d403a7a74e8e9b9d343
|8,1=>0xd627ab8f559ea83d4a7a88f4f9e9c3d327a58f499e903d1a7a28f439e843d0279f8f3d9e783cea79c8f379e6c3cd27998f319e603cba7968f2b9e543ca27938f259e483c8a7908f1f9e3c3c7278d8f199e303c5a78a8f139e243c427878f0d9e183c2a7848f079e0c3c127818f019e003bfa77e8efb9df43
|8,2=>0xee27db8fb59f683eca7d88faf9f5c3eb27d58fa99f503e9a7d28fa39f443e827cf8f9d9f383e6a7cc8f979f2c3e527c98f919f203e3a7c68f8b9f143e227c38f859f083e0a7c08f7f9efc3df27bd8f799ef03dda7ba8f739ee43dc27b78f6d9ed83daa7b48f679ecc3d927b18f619ec03d7a7ae8f5b9eb43
|8,3=>0x1de8fbb9f743
|9,0=>0xfc65f84bef97dd2fb65f64beb97d52fa65f44be797cd2f965f24be397c52f865f04bdf97bd2f765ee4bdb97b52f665ec4bd797ad2f565ea4bd397a52f465e84bcf979d2f365e64bcb97952f265e44bc7978d2f165e24bc397852f065e04bbf977d2
|10,0=>0xfd83fac7f50fe91fd03f9c7f30fe51
|11,0=>0x7ed0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 18 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 255), wireSAt ((code >>> 10) &&& 255)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 15 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmB : Nat → Nat → Nat
|4,0=>0x10000000
|5,0=>0x14000000000100000000000000000000000000000000010000000000400000000000000000000000000140000420001000000000000000000
|6,0=>0x28000100000000000000000000000000042000000000000000000002800000000100000000000000080000000004019c00000008000100530000000000000010000000000000000280000000000000000000043000020000080005000000000000000000000020000000082000010300010000010000100000a0000000000f8000000000000000200000000000000000000418000020000001010300010800000000118000000000000200a000024000d800020800008000020000800000000000000000800008000000000090000000000000000000000040114000000000200000000000000013000084100430001000000000000000000000000020000002000000604043c0000000002000046000000000280000a00000000000000000000020000000000010012400000000000
|7,0=>0x802040065000020000280000200013f00025800082000020000ee020005001021001140000900002400002000118000420000000900100000080008000084000210000800212c4801280000a00010000086000084000c00001180000810019400000008250000080002210012c0084400000100058800001000000000c20000080201000008000001000088080200080000001608010000040008040000420403bca0068840134000890000200010200000000008000150000200002280002100840000082000040000400001200207e00020c000fd84013c0200010001c80102000020001770000084004200018000000020024000420000a10000000002000040000208000020000840009600010000008000004000a800002400040000020000010000580008800002000001020020000d400002000028080200001ab10010800050400600000a040002000086000320020220000244002000840800016
|7,1=>0x10c8804500070800005000104000080001180001620000000008000020004040004148000a000020000010000040009800004800001000058000ce00015c60040000020000e70000800000000000000002000000080090000200008600860000054020004000400000201004d02000480062000000000080002ec0000100061000107000100080010000050000d000004000160000a000003000008000000080a0000010084f4000ff0000084086700002128042000850000400003181012f00003c0008f00020800021000080000880000a0400820000040000200002000000000100000160000a0000080002580000800000800008000004000022085dc0004310219c000460000008000a0001080000100010000046000020100fb00000000002000258000c60002200002000017000000000020000200000800002800001c00008000008000220000000013f0002b80004004036c0001600002000001
|7,2=>0x800000000004000400002200018600845000007000118000080000000004200011800001
|8,0=>0x5b60802940043c000ff0806540007f000114c007f40003e0007f02023c000ff0006bc001220003fc0807f8003b4a00600804a8400ef82009c001ef9000be00165c001be2006a1203fc100ef200720000ff4000b42012540042808009000422000cf000734080ef2007bc000ed0003fc002fd0203bc201ef000429000af100109001ca2000f4800480001fc000cd020354400ef2007348007f0802b40007f2005340816d0201bc001af4005fc080ef0201b58002d000184001688001a02012f0200a4080f7800108020f700037c00068880180000fd020224000ff020336480ff000320400ed6005882012f0004fc100ed2003e8880453801a0080299200a4001ef0003fe000af02018e480890005b5001cf2001808002d0003fd000030003fc400658003a9001aa0006bc0013f400794000ed000df4000ff2005b4080ff900024008efc0839c008ed6001a1280422203b4e004a0003ff801052001be0002a
|8,1=>0x12f000100000af0004bc001ff0003b4000ed2007fc8000f020105280582003be400ff1001960802f000334000a80003f44802f0007b4000c2600758800ed0203bc00041020154000ff0081fc800ed02026128048480528000ed2805a0000fd0203dc000481a039c080670003f6400ed0203bc080ff880100a0068000420001ed0201fc8015aa00100000cb0003f40012f900224200250003b48002a0002e0000ff02039c000e2020224020d80007fc0000a4803a2040ff
|9,0=>0x203b4801ff2005b4000ef4007bc201ed2005fc000fd8001bc080ff0007b4080ef0003fc400ef0007b4000ef0003fc0007f02031c080cf1203bd001ed0201148007fa001b4080ef0004bc881ed8203be400ef0203bc000ef1003bd001ef8003b4801ff3801b4000ed1003fc201ef0003fc000ff2001b40016f1003b50012f0003fd0017f0201fd001fd4a013c000ef
|10,0=>0x201bc000ff2007b4000ef4005bc000ef0001fc000ed
|11,0=>0x6f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 22 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_243,10,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 1 then [(dom_235,10,runOps true dom_235 (0,roots_235) ops)] else [])++(if pm.testBit 2 then [(dom_219,10,runOps true dom_219 (0,roots_219) ops)] else [])++(if pm.testBit 3 then [(dom_250,9,runOps true dom_250 (0,roots_250) ops)] else [])++(if pm.testBit 4 then [(dzo_235_16,9,runOps true dzo_235_16 (0,roots_235) ops)] else [])++(if pm.testBit 5 then [(dom_123,9,runOps true dom_123 (0,roots_123) ops)] else [])++(if pm.testBit 6 then [(dom_233,8,runOps true dom_233 (0,roots_233) ops)] else [])++(if pm.testBit 7 then [(dom_187,8,runOps true dom_187 (0,roots_187) ops)] else [])++(if pm.testBit 8 then [(dzo_249_2,7,runOps true dzo_249_2 (0,roots_249) ops)] else [])++(if pm.testBit 9 then [(dom_234,7,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 10 then [(dom_225,7,runOps true dom_225 (0,roots_225) ops)] else [])++(if pm.testBit 11 then [(dom_179,7,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 12 then [(dom_115,7,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 13 then [(dom_171,7,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 14 then [(dom_107,7,runOps true dom_107 (0,roots_107) ops)] else [])++(if pm.testBit 15 then [(dom_122,6,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 16 then [(dom_155,6,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 17 then [(dom_232,5,runOps true dom_232 (0,roots_232) ops)] else [])++(if pm.testBit 18 then [(dom_186,5,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 19 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 20 then [(dom_105,5,runOps true dom_105 (0,roots_105) ops)] else [])++(if pm.testBit 21 then [(dom_59,5,runOps true dom_59 (0,roots_59) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_251 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_243 _ g hchk
    · exact cpcs (by decide +kernel) low_235 _ g hchk
    · exact cpcs (by decide +kernel) low_219 _ g hchk
    · exact cpcs (by decide +kernel) low_250 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_235_16_2 _ g hchk
    · exact cpcs (by decide +kernel) low_123 _ g hchk
    · exact cpcs (by decide +kernel) low_233 _ g hchk
    · exact cpcs (by decide +kernel) low_187 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_249_2_112 _ g hchk
    · exact cpcs (by decide +kernel) low_234 _ g hchk
    · exact cpcs (by decide +kernel) low_225 _ g hchk
    · exact cpcs (by decide +kernel) low_179 _ g hchk
    · exact cpcs (by decide +kernel) low_115 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_107 _ g hchk
    · exact cpcs (by decide +kernel) low_122 _ g hchk
    · exact cpcs (by decide +kernel) low_155 _ g hchk
    · exact cpcs (by decide +kernel) low_232 _ g hchk
    · exact cpcs (by decide +kernel) low_186 _ g hchk
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) low_105 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_243 10 s (0, roots_243) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_243 h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_251 == dom_251) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_251 goalM v ys) : RunD true dom_251 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_251 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_12 : ∀ i, 12 ≤ i → i < 22 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 22 → Z 5 i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_36 : ∀ i, 36 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_48 : ∀ i, 48 ≤ i → i < 60 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 48 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_60 : ∀ i, 60 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 60 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_72 : ∀ i, 72 ≤ i → i < 84 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 72 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_84 : ∀ i, 84 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 84 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_96 : ∀ i, 96 ≤ i → i < 108 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 96 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_108 : ∀ i, 108 ≤ i → i < 111 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 108 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 111 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) z6_24) z6_36) z6_48) z6_60) z6_72) z6_84) z6_96) z6_108)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7_264 : ∀ i, 264 ≤ i → i < 270 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 264 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 270 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) z7_24) z7_36) z7_48) z7_60) z7_72) z7_84) z7_96) z7_108) z7_120) z7_132) z7_144) z7_156) z7_168) z7_180) z7_192) z7_204) z7_216) z7_228) z7_240) z7_252) z7_264)
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8_192 : ∀ i, 192 ≤ i → i < 195 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 192 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 195 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z8_0 z8_12) z8_24) z8_36) z8_48) z8_60) z8_72) z8_84) z8_96) z8_108) z8_120) z8_132) z8_144) z8_156) z8_168) z8_180) z8_192)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_0 : ∀ i, 0 ≤ i → i < 12 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_12 : ∀ i, 12 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 12 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_24 : ∀ i, 24 ≤ i → i < 36 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 24 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_36 : ∀ i, 36 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 12 36 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9_48 : ∀ i, 48 ≤ i → i < 52 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 48 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 52 → Z 9 i = true := (range_split (range_split (range_split (range_split z9_0 z9_12) z9_24) z9_36) z9_48)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
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
    [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 32, 36)] (by decide +kernel) (by decide +kernel) low_251

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 13 := low_255

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [6, 8] }, { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.and, inputs := [9, 10] }, { op := GateOp.or, inputs := [1, 8] }, { op := GateOp.and, inputs := [6, 12] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [14, 15] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [1, 17] }, { op := GateOp.or, inputs := [11, 13] }, { op := GateOp.or, inputs := [16, 19] }, { op := GateOp.or, inputs := [18, 20] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_30859_aux

theorem PEqualNP.Outside.L_meta_30859 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_30859_aux.main
