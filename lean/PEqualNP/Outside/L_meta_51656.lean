import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51656_aux
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
def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000eeeeeeeecccc0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0xffccffcccccc0000ffccffcccccc0000ffccffcccccc0000ffccffcccccc0000
def roots_58 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_75 : Nat := 0xf0f0000000000000f0f
def goal_75 : Nat := 0xeeeeeeeeeeeeeeeeaa00aa00aa00aa00eeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_75 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaaaaffffaaaaaa00aa00aa00aa00ffffaaaaffffaaaaaa00aa00aa00aa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeeeffffeeeeeeccaa00eeccaa00ffffeeeeffffeeeeeeccaa00eeccaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaaaaaaaaaffaaffaaaa00aa00ffaaffaaaaaaaaaaffaaffaaaa00aa00
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccccccccccffccffcc00000000ffccffccccccccccffccffcc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeeeeeeeeeffeeffeeaa00aa00ffeeffeeeeeeeeeeffeeffeeaa00aa00
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffeeeeeeeeeeeecccc0000ffffeeeeffffeeeeeeeeeeeecccc0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffaaaaffaaffaaaa00aa00ffffffaaffffaaaaffaaffaaaa00aa00
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_122 : Nat := 0x5050505050505050505050505050505
def goal_122 : Nat := 0xffffffccffffccccffccffcccccc0000ffffffccffffccccffccffcccccc0000
def roots_122 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffeeeeffeeffeeeeccaa00ffffffeeffffeeeeffeeffeeeeccaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffeeccffffeeccffffeeccffffeecceeccaa00eeccaa00eeccaa00eeccaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffccccccccffffffffcccccccceeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffaa00aa00ffffffffaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def goal_170 : Nat := 0xffffffffccccccccffffffffccccccccffccffcc00000000ffccffcc00000000
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffeecceeccffffffffeecceeccffeeffeeaa00aa00ffeeffeeaa00aa00
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffff0000ffffffffffff0000aaaaaaaa00000000aaaaaaaa00000000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffffffccccffffffffffffcccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffffffccccffffffffffffcccceeeeeeeecccc0000eeeeeeeecccc0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def goal_184 : Nat := 0xffffffffffff0000ffffffffffff0000ff00ff0000000000ff00ff0000000000
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffaa00ffffffffffffaa00ffaaffaaaa00aa00ffaaffaaaa00aa00
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffffccccffffffffffffccccffccffcccccc0000ffccffcccccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffffeeccffffffffffffeeccffeeffeeeeccaa00ffeeffeeeeccaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_194 : Nat := 0x5000000000000000500000000000000050000000000000005
def goal_194 : Nat := 0xffffffffffffffffcccccccccccccccccccccccccccccccc0000000000000000
def roots_194 : List Nat := [xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffffffffffffffffaa00aa00aa00aa00aaaaaaaaaaaaaaaaaa00aa00aa00aa00
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffffffffffffffffeecceecceecceecceeeeeeeeeeeeeeeeaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_208 : Nat := 0x10001000000000001000100000000000100010000000000010001
def goal_208 : Nat := 0xffffffffffffffffffff0000ffff0000ffff0000ffff00000000000000000000
def roots_208 : List Nat := [xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffffffffffffffffffccccffffccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffffffffffffffffffccccffffccccffffeeeeffffeeeecccc0000cccc0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffffffffffffffffaa00ffffaa00ffffaaaaffffaaaaaa00aa00aa00aa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffffffffffffffffeeccffffeeccffffeeeeffffeeeeeeccaa00eeccaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffffffffffffffffff00000000ff00ff0000000000ff00ff0000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffffffffffffffffccccccccffccffccccccccccffccffcc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffffffffffffffffeecceeccffeeffeeeeeeeeeeffeeffeeaa00aa00
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffffffffffffffffffccccffffccccffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffffffffffffffffffccccffffeeeeffffeeeeeeeeeeeecccc0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffffffffffffffffff0000ffffff00ffff0000ff00ff0000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffffffffffffffffaa00ffffffaaffffaaaaffaaffaaaa00aa00
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffffffffffffffffccccffffffccffffccccffccffcccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffffffffffffffffeeccffffffeeffffeeeeffeeffeeeeccaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffffffffffffffffefcfffffffefffffefeffeeffeeeeccaa00
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_41
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (8,9), (8,40), (32,33), (32,40)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_41.map (· &&& dom_41)
def goalM : Nat := goal_41 &&& dom_41
def NN : Nat → Nat
|2=>1
|3=>1
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
|2,0=>3
|3,0=>0x33
|_,_=>0
def dictMask : Nat := 0x3ffffffffff
def wireSAt (i : Nat) : Nat := if i < 3 then (dictB (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& dictMask else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_41 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_41 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
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

theorem lowS_41 : Lower true dom_41 roots_41 goal_41 4 := S_41.noCircuit

def isoMvS_82 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_82 : Lower true dom_82 roots_82 goal_82 4 :=
  lower_iso isoMvS_82 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41

def isoMvS_146 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_146 : Lower true dom_146 roots_146 goal_146 4 :=
  lower_iso isoMvS_146 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41

def isoMvS_162 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_162 : Lower true dom_162 roots_162 goal_162 4 :=
  lower_iso isoMvS_162 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41

def isoMvS_194 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_194 : Lower true dom_194 roots_194 goal_194 4 :=
  lower_iso isoMvS_194 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41

def isoMvS_208 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_208 : Lower true dom_208 roots_208 goal_208 4 :=
  lower_iso isoMvS_208 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41

theorem lowS_43 : Lower true dom_43 roots_43 goal_43 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_41

namespace S_51
def pairsG : List (Nat × Nat) := [(1,33), (2,18), (2,34), (3,19), (3,35), (16,18), (17,19), (17,49), (32,33), (32,34), (48,49), (48,50)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
|3=>1
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
|3,0=>4
|_,_=>0
def dictMask : Nat := 0xfffffffffffff
def wireSAt (i : Nat) : Nat := if i < 4 then (dictB (i / 512) (i / 32 % 16) >>> (52 * (i % 32))) &&& dictMask else 0
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
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_51 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_51 goalM v ys := by simp [cutRoot] at h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
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

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 4 := S_51.noCircuit

theorem lowS_178 : Lower true dom_178 roots_178 goal_178 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500000005000000000000000000000005000000050000, 2, 18)] (by decide +kernel) (by decide +kernel) lowS_162

namespace S_210
def pairsG : List (Nat × Nat) := [(2,18), (2,66), (2,130), (16,18), (16,80), (16,144), (64,66), (64,80), (64,192), (128,130), (128,144), (128,192)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_210.map (· &&& dom_210)
def goalM : Nat := goal_210 &&& dom_210
def NN : Nat → Nat
|3=>3
|4=>7
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x2734b1484106337
|4,0=>0x512cb4fced48dad438ab2196b14487088b7
|5,0=>0xf05418f1f927ca3
|6,0=>0xf0541
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa000800000000000a000800000000000000014001400000000000000000000000000100010000000000000000280028000000000000000000000000002800050005000000000005000500000000000400040000000000040004a000800000000000a000800000000000a000800000000000a000940014000000000010001000000000001400140000000000100012800280000000000280028000000000028002800000000002800050005000000000005000000000000000500050000000000050000a000a00000000000a000a00000000000a000000000000000a000140014000000000014001400000000001400140000000000000000000000000000000000000000000000028002800000000002800250005000000000000000000000000000500050000000000000000a000000000000000a000000000000000a000000000000000a000100010000000000010001000000000001000100000000000100012800280000000000000000000000000028002000000000000000050005000000000005000500000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x324032403a24032640f324032e403d240832603c264b3a4093240872653243210
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x21022004
|4,0=>0xa952aa0536a5948a8c5
|5,0=>0xe51a2af5
|6,0=>0x3d4
|_,_=>0
def dictMask : Nat := 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 16 then (dictB (i / 512) (i / 32 % 16) >>> (211 * (i % 32))) &&& dictMask else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 11 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))

def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x4250134501205013250930501
|_=>0
def opOffB : Nat → Nat → Nat
|3,0=>0x20000
|4,0=>0x62422200
|5,0=>0x9181
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
|0=>0xfa7650
|_=>0
def pmB : Nat → Nat → Nat
|3,0=>0x80
|4,0=>0x850
|5,0=>0xed
|6,0=>5
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_208,4,runOps true dom_208 (0,roots_208) ops)] else [])++(if pm.testBit 1 then [(dom_194,4,runOps true dom_194 (0,roots_194) ops)] else [])++(if pm.testBit 2 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 3 then [(dom_82,4,runOps true dom_82 (0,roots_82) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_210 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_208 _ g hchk
    · exact cpcs (by decide +kernel) lowS_194 _ g hchk
    · exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_82 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_208 4 s (0, roots_208) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_210 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_208 h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xcccccccccccccccccccccccccccccccc, 126)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_210 == dom_210) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_210 goalM v ys) : RunD true dom_210 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_210 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 7 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_210 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_210 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_210 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_210 roots_210 goal_210 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_210

theorem lowS_210 : Lower true dom_210 roots_210 goal_210 7 := S_210.noCircuit

def isoMvS_58 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_58 : Lower true dom_58 roots_58 goal_58 4 :=
  lower_iso isoMvS_58 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_75 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_75 : Lower true dom_75 roots_75 goal_75 4 :=
  lower_iso isoMvS_75 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_89 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_89 : Lower true dom_89 roots_89 goal_89 4 :=
  lower_iso isoMvS_89 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_105 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_105 : Lower true dom_105 roots_105 goal_105 5 :=
  lower_iso isoMvS_105 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43

def isoMvS_106 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_106 : Lower true dom_106 roots_106 goal_106 4 :=
  lower_iso isoMvS_106 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_163 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_iso isoMvS_163 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43

def isoMvS_169 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_iso isoMvS_169 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43

def isoMvS_170 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_170 : Lower true dom_170 roots_170 goal_170 5 :=
  lower_iso isoMvS_170 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43

def isoMvS_177 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_177 : Lower true dom_177 roots_177 goal_177 4 :=
  lower_iso isoMvS_177 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_184 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_184 : Lower true dom_184 roots_184 goal_184 4 :=
  lower_iso isoMvS_184 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_201 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_201 : Lower true dom_201 roots_201 goal_201 4 :=
  lower_iso isoMvS_201 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_232 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_232 : Lower true dom_232 roots_232 goal_232 4 :=
  lower_iso isoMvS_232 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16:=0xf0e00000e0c0000
def gsh_43_16:=0xf0e00000e0c
theorem lowS_zo_43_16_41:Lower true dzo_43_16 roots_43 gzo_43_16 5:=lower_iso (d1:=dom_43) (roots1:=roots_43) (T1:=gsh_43_16) [(dom_43,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_43_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c00000c0c,0,2)] (by decide +kernel) (by decide +kernel) lowS_41)
namespace S_59
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (2,18), (2,34), (3,11), (3,19), (3,35), (8,9), (8,40), (10,11), (10,26), (10,42), (16,18), (17,19), (17,25), (17,49), (24,25), (24,26), (24,56), (32,33), (32,34), (32,40), (48,49), (48,50), (48,56)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
|4=>2
|5=>3
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xe51f9284fe
|5,0=>0x3f26a21e3d17d13
|6,0=>0x260ba
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0a0f0a0f0a0f0a505050500000000f0f0f0f0f000f00f000f000f000f0000f000f000a000af0f0f0f00000000f0f00000f0f0000f000f000a000a00c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x436104396104361087436104310543210
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x15405
|5,0=>0x166418a6
|6,0=>0x1c5
|_,_=>0
def dictMask : Nat := 0xfffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 10 then (dictB (i / 512) (i / 32 % 16) >>> (60 * (i % 32))) &&& dictMask else 0
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
|0=>0x103
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
|0=>0x1f59040
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
    (if pm.testBit 0 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 1 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])++(if pm.testBit 2 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 3 then [(dzo_43_16,5,runOps true dzo_43_16 (0,roots_43) ops)] else [])++(if pm.testBit 4 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_59 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_41 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_43 5 s (0, roots_43) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_59 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_43 h

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59 == dom_59) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_59 goalM v ys) : RunD true dom_59 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_59 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_59 roots_59 goal_59 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_59

theorem lowS_59 : Lower true dom_59 roots_59 goal_59 7 := S_59.noCircuit

theorem lowS_107 : Lower true dom_107 roots_107 goal_107 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_105

theorem lowS_155 : Lower true dom_155 roots_155 goal_155 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0000000000000000000000000a0a0a0a, 8, 9), (0xf000f000000000000000000000000000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) lowS_146

namespace S_171
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (2,34), (2,130), (3,11), (3,35), (3,131), (8,9), (8,40), (10,11), (10,42), (10,138), (32,33), (32,34), (32,40), (32,160), (128,130), (128,160), (129,131), (129,137), (129,161), (136,137), (136,138), (136,168)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_171.map (· &&& dom_171)
def goalM : Nat := goal_171 &&& dom_171
def NN : Nat → Nat
|3=>1
|4=>4
|5=>10
|6=>4
|7=>1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0xb8b1
|4,0=>0x41dd4398282645b24a07
|5,0=>0x94b1652a6c391562787c2454020fae203f6167de132f20424f
|6,0=>0xb1bca1438e0544104b0f
|7,0=>0xb1bca
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f00000c0c000000000000000000000f0f00000c0c00f0000000000000000000000000000000f00000000f0f00000f00000000000000000000000f0f00000f00505000005000000000000000000000005050000050000000000000000000000000000000000f0f00000c0cf0300000f00000000000000000000000f0300000f001010000000000000000000000000000010100000000e0e00000e0e000000000000000000000e0e00000e0e00000000f0c00000000000000000000000000000f0cf0c00000f0c000000000000000000000f0c00000f0cf0c00000000000000000000000000000f0c00000000f0f00000a0a000000000000000000000f0f00000a0a5050000000000000000000000000000050500000000f0f00000f0f000000000000000000000f0000000f00f0f00000f0f000000000000000000000f0f00000f0000000000000000000000000000000000f0f00000f00f0f00000000000000000000000000000a0a000000003030000030300000000000000000000010100000000f0e00000f00000000000000000000000f0e00000f00f0f00000000000000000000000000000f0f00000000c0c00000c0c000000000000000000000c0c00000c0c5050000050500000000000000000000050500000500f0f00000f0f00000000000000000000000000000000f0f00000f0f000000000000000000000f0f00000000f0f00000c0c000000000000000000000f0c00000c0cf0000000f00000000000000000000000f0000000f00a0a00000a0a000000000000000000000a0a00000a0a
|_,_=>0
def stPool : Nat → Nat
|0=>0x1c26010e130087884c0268e13008709819260e135c96384c03d426010e13028479c33310e1302443c026011e7099c461c260116709804184c051c20490e830087098a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>4
|4,0=>0x26a3944a845
|5,0=>0x26b48584cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 27 then (dictB (i / 512) (i / 32 % 16) >>> (172 * (i % 32))) &&& dictMask else 0
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
|0=>0x305399387c0338539b3813c43b5
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x42003100210011000100
|6,0=>0x817161
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
|0=>0x3ff7be5e489183080
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x4010506230
|6,0=>0x7a98
|7,0=>0xa
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 4 (j % 128); fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 1 then [(dom_162,4,runOps true dom_162 (0,roots_162) ops)] else [])++(if pm.testBit 2 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])++(if pm.testBit 3 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 4 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 5 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_171 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · exact cpcs (by decide +kernel) lowS_162 _ g hchk
    · exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · exact cpcs (by decide +kernel) lowS_169 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_170 5 s (0, roots_170) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_171 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_170 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_171 == dom_171) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_171 goalM v ys) : RunD true dom_171 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_171 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_171 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
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
  scr true dom_171 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_171 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_171 roots_171 goal_171 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull

end S_171

theorem lowS_171 : Lower true dom_171 roots_171 goal_171 8 := S_171.noCircuit

def dzo_178_1:=0xa000a000a000a0000000000000000000a000a000a000a
def gzo_178_1:=0xa000a000a00080000000000000000000a000a00080000
def gsh_178_1:=0x500050005000400000000000000000005000500040000
theorem lowS_zo_178_1_146:Lower true dzo_178_1 roots_178 gzo_178_1 5:=lower_iso (d1:=dom_178) (roots1:=roots_178) (T1:=gsh_178_1) [(dom_178,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_178_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500050000000000000000000000000005000500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_146)
namespace S_179
def pairsG : List (Nat × Nat) := [(1,33), (2,18), (2,34), (2,130), (3,19), (3,35), (3,131), (16,18), (16,144), (17,19), (17,49), (17,145), (32,33), (32,34), (32,160), (48,49), (48,50), (48,176), (128,130), (128,144), (128,160), (129,131), (129,145), (129,161)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_179.map (· &&& dom_179)
def goalM : Nat := goal_179 &&& dom_179
def NN : Nat → Nat
|4=>1
|5=>1
|6=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x33c24
|5,0=>0x4d505
|6,0=>0x1d437
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0000000f00000000000000000000000f0000000f0000f000f000f000f0000000000000000000c000c000c000cf000f000000000000000000000000000f000f00000000c000c000c000c0000000000000000000c000c000c000ca000a000a000a0000000000000000000a000a000a000a0000f0000000f00000000000000000000000c0000000cf000f000f000f00000000000000000000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x99a135684688
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>5
|5,0=>0x56
|6,0=>0xb5
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 7 then (dictB (i / 512) (i / 32 % 16) >>> (180 * (i % 32))) &&& dictMask else 0
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
|0=>0x61
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
    (if pm.testBit 0 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 1 then [(dom_177,4,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 2 then [(dzo_178_1,5,runOps true dzo_178_1 (0,roots_178) ops)] else [])++(if pm.testBit 3 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 4 then [(dom_51,4,runOps true dom_51 (0,roots_51) ops)] else [])++(if pm.testBit 5 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])
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
    · exact cpcs (by decide +kernel) lowS_177 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_178_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_163 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_146 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_178 5 s (0, roots_178) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_179 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_178 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_179 == dom_179) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_179 goalM v ys) : RunD true dom_179 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 7 := S_179.noCircuit

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a00000000000a000a00000000000a000a, 64, 65)] (by decide +kernel) (by decide +kernel) lowS_210

theorem lowS_214 : Lower true dom_214 roots_214 goal_214 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050000000000050005000000000005000500000000000500050, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_210

def isoMvS_91 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_91 : Lower true dom_91 roots_91 goal_91 7 :=
  lower_iso isoMvS_91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def isoMvS_115 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_115 : Lower true dom_115 roots_115 goal_115 6 :=
  lower_iso isoMvS_115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_107

def isoMvS_121 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_121 : Lower true dom_121 roots_121 goal_121 7 :=
  lower_iso isoMvS_121 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def isoMvS_122 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_122 : Lower true dom_122 roots_122 goal_122 7 :=
  lower_iso isoMvS_122 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def isoMvS_185 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_185 : Lower true dom_185 roots_185 goal_185 7 :=
  lower_iso isoMvS_185 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def isoMvS_186 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_186 : Lower true dom_186 roots_186 goal_186 7 :=
  lower_iso isoMvS_186 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179

def isoMvS_203 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_203 : Lower true dom_203 roots_203 goal_203 7 :=
  lower_iso isoMvS_203 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def isoMvS_217 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 :=
  lower_iso isoMvS_217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def isoMvS_234 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 7 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179

def isoMvS_242 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 8 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_214

def isoMvS_248 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_248 : Lower true dom_248 roots_248 goal_248 7 :=
  lower_iso isoMvS_248 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59

def dzo_115_8:=0xf000f000f000f000f000f000f000f00
def gzo_115_8:=0xf000f000f000e000f000f000e000a00
def gsh_115_8:=0xf000f000f000e000f000f000e000a
theorem lowS_zo_115_8_82:Lower true dzo_115_8 roots_115 gzo_115_8 6:=lower_iso (d1:=dom_115) (roots1:=roots_115) (T1:=gsh_115_8) [(dom_115,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_115_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_82)
namespace S_123
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,18), (2,34), (2,66), (3,11), (3,19), (3,35), (3,67), (8,9), (8,40), (10,11), (10,26), (10,42), (10,74), (16,18), (16,80), (17,19), (17,25), (17,49), (17,81), (24,25), (24,26), (24,56), (24,88), (32,33), (32,34), (32,40), (48,49), (48,50), (48,56), (48,112), (64,65), (64,66), (64,80), (72,73), (72,74), (72,88), (72,104), (96,97), (96,98), (96,104), (96,112)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_123.map (· &&& dom_123)
def goalM : Nat := goal_123 &&& dom_123
def NN : Nat → Nat
|8=>1
|_=>0
def HT : Nat → Nat → Nat
|8,0=>0x528e8
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f000000000f0f0f0f00000000f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x2c688
|_=>0
def stOffB : Nat → Nat → Nat
|8,0=>6
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 6 then (dictB (i / 512) (i / 32 % 16) >>> (124 * (i % 32))) &&& dictMask else 0
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
|0=>0x3f80
|_=>0
def pmB : Nat → Nat → Nat
|8,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 1 (j % 128); fld (pmPalB (k / 32)) 7 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_122,7,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 1 then [(dom_121,7,runOps true dom_121 (0,roots_121) ops)] else [])++(if pm.testBit 2 then [(dom_59,7,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 3 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 4 then [(dom_115,6,runOps true dom_115 (0,roots_115) ops)] else [])++(if pm.testBit 5 then [(dzo_115_8,6,runOps true dzo_115_8 (0,roots_115) ops)] else [])++(if pm.testBit 6 then [(dom_107,6,runOps true dom_107 (0,roots_107) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_123 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_115 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_115_8_82 _ g hchk
    · exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_122 7 s (0, roots_122) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_123 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_122 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_123 == dom_123) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_123 goalM v ys) : RunD true dom_123 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_123 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega
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

theorem lowS_123 : Lower true dom_123 roots_123 goal_123 9 := S_123.noCircuit

def dzo_41_16:=0x303000003030000
def gzo_41_16:=0x302000002000000
def gsh_41_16:=0x30200000200
theorem lowS_zo_41_16_41:Lower true dzo_41_16 roots_41 gzo_41_16 4:=lower_iso (d1:=dom_41) (roots1:=roots_41) (T1:=gsh_41_16) [(dom_41,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_41_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [] (by decide +kernel) (by decide +kernel) lowS_41)
def dzo_171_16:=0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0c0000
def gsh_171_16:=0xf0f00000f0f000000000000000000000f0e00000e0c
theorem lowS_zo_171_16_41:Lower true dzo_171_16 roots_171 gzo_171_16 6:=lower_iso (d1:=dom_171) (roots1:=roots_171) (T1:=gsh_171_16) [(dom_171,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_171_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c00000c0c000000000000000000000c0c00000c0c,0,2),(0xf0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_41)
def dzo_169_16:=0x30300000303000000000000000000000303000003030000
def gzo_169_16:=0x30300000303000000000000000000000302000002000000
def gsh_169_16:=0x3030000030300000000000000000000030200000200
theorem lowS_zo_169_16_41:Lower true dzo_169_16 roots_169 gzo_169_16 5:=lower_iso (d1:=dom_169) (roots1:=roots_169) (T1:=gsh_169_16) [(dom_169,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_169_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x3030000030300000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_41)
def dzo_154_1:=0xa0a0a0a0000000000000000000000000a0a0a0a
def gzo_154_1:=0xa0a0a080000000000000000000000000a080a00
def gsh_154_1:=0x505050400000000000000000000000005040500
theorem lowS_zo_154_1_146:Lower true dzo_154_1 roots_154 gzo_154_1 5:=lower_iso (d1:=dom_154) (roots1:=roots_154) (T1:=gsh_154_1) [(dom_154,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_154_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x500050000000000000000000000000005000500,0,8)] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_147_8:=0xf000f000000000000000000000000000f000f00
def gzo_147_8:=0xf000e000000000000000000000000000e000a00
def gsh_147_8:=0xf000e000000000000000000000000000e000a
theorem lowS_zo_147_8_146:Lower true dzo_147_8 roots_147 gzo_147_8 5:=lower_iso (d1:=dom_147) (roots1:=roots_147) (T1:=gsh_147_8) [(dom_147,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_147_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a000000000000000000000000000a000a,0,1)] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_179_8:=0xf000f000f000f0000000000000000000f000f000f000f00
def gzo_179_8:=0xf000f000f000e0000000000000000000f000f000e000a00
def gsh_179_8:=0xf000f000f000e0000000000000000000f000f000e000a
theorem lowS_zo_179_8_146:Lower true dzo_179_8 roots_179 gzo_179_8 6:=lower_iso (d1:=dom_179) (roots1:=roots_179) (T1:=gsh_179_8) [(dom_179,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_179_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a000a000a0000000000000000000a000a000a000a,0,1),(0xf000f000000000000000000000000000f000f00000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_146)
def dzo_186_1:=0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a
def gzo_186_1:=0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a00
def gsh_186_1:=0x50505050505050400000000000000000505050505040500
theorem lowS_zo_186_1_146:Lower true dzo_186_1 roots_186 gzo_186_1 6:=lower_iso (d1:=dom_186) (roots1:=roots_186) (T1:=gsh_186_1) [(dom_186,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_186_1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x50005000500050000000000000000000500050005000500,0,8),(0x50505050000000000000000000000000505050500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_146)
namespace S_187
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (2,18), (2,34), (2,130), (3,11), (3,19), (3,35), (3,131), (8,9), (8,40), (10,11), (10,26), (10,42), (10,138), (16,18), (16,144), (17,19), (17,25), (17,49), (17,145), (24,25), (24,26), (24,56), (24,152), (32,33), (32,34), (32,40), (32,160), (48,49), (48,50), (48,56), (48,176), (128,130), (128,144), (128,160), (129,131), (129,137), (129,145), (129,161), (136,137), (136,138), (136,152), (136,168)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_187.map (· &&& dom_187)
def goalM : Nat := goal_187 &&& dom_187
def NN : Nat → Nat
|5=>4
|6=>15
|7=>24
|8=>8
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|5,0=>0xb403676e8067e4104acb
|6,0=>0xf1900ed5fad87f9cd28791cab8756885a32454cf335012b90d2344f1f4981b36410733038b6
|7,0=>0xbad47a6c29a3ff7a0eb490bdc8fea38b40485760754816ad3e61f475d6e856d4656a3052a404f44a3aa1437fa31593e10aea0dbc80cee60b3b002025
|8,0=>0xe3d16c44d3c41bdc01cdad089821e57300e149e4
|9,0=>0xe079b
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f0f0f000000000000000000000f0f0f0f0f0f0000c0c0c0c0c0c0c0c00000000000000000f0f0f0f0c0c0c0c00000000000000000000000000000000f0f0f0f00000000f0f05050f0f000000000000000000000f0f05050f0f0000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a3030303030303030000000000000000020202020202020250505050000000000000000000000000505050500000000f0f0f0f0f0f0f0f00000000000000000505050500000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0af0f0f0f00000f0f00000000000000000f0f0f0f00000c0cf0f0f0f0f0f0f0f0000000000000000000f000f00000000f0f0f0f0f0f0f0f00000000000000000c0f0c0f0c0c0c0cf0f0f0f0f000f0000000000000000000f0f0f0f0f000f00a0a0a0a0a000a0000000000000000000a0a0a0a0a000a00f0f0f0f0c0c0c0c00000000000000000f0f0f0f0c0c0c0cf0f0f0f0f0f0f0f00000000000000000f0f0f0f0c0c0c0c00f000f000000000000000000000000000f000f00000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000f0f0f0f0f0f0f0f00000000000000000c0c0c0c0c0c0c0c3030303030303030000000000000000010101010000000000000000000000000000000000000000f0f0f0f0c0c0c0cf0f00000f0f000000000000000000000f0f00000f0f00003030303030303030000000000000000030303030000000000f0f0f00000f0f0000000000000000000f0c0f00000c0cf000f000f000f0000000000000000000f000f000f000f0050505050500050000000000000000000505050505000500f0f0f0f0000000000000000000000000f0f0f0f00000000f000f000a000a0000000000000000000f000f000a000a00c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a0000f0f00000f0f000000000000000000000c0c00000c0cf0f0f0f0f0f0f0f00000000000000000000000000000000
|0,1=>0xf0f0f0f0f0f0f0f00000000000000000f000f000f000f0030303030000000000000000000000000303030300000000f0f0f0f0f0f0f0f00000000000000000e0e0e0e0e0e0e0ef0f00000f0f000000000000000000000f0f0f0f0f0f000000000000000000000000000000000000303030300000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x131470c20401571c30810161470c200528734318044e28734244e14a1cd09114a1c224044b38a1c308528734309514a1d40c200528734348040b14a1c30851c308f0403852873422452870c23002c52870891470c22001470c60401440c2040
|1=>0x52870c28007d11470c201138a1c308044e14a1c30807852870c201174a1c30804c528734308014a1cd0c264014a5c73430804052870c20052870c60103852870c20057070c20052870c26801470c20403852873430852870c224014a1c3098
|2=>0x52870c201f1470c201314a1c308014a1c30990052971c308014a1c30a301114a1c308014a1cd0c20052a41c30807c70c28c014a1e20c20211470c20112c52870c20052870d201f4470c2
|_=>0
def stOffB : Nat → Nat → Nat
|5,0=>0x9303180cc006
|6,0=>0x1e1ce2e6b63239798aee50724b909c76e34716b899c3ee187
|7,0=>0x903465e26d0b882b3fd9f0ef17753b8a1b6ed476643121790b5757b29e142c9a74a3235d0ce7f7
|8,0=>0xabb541e92f4279dbcd1e5af267
|9,0=>0x15d6
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 37 then (dictB (i / 512) (i / 32 % 16) >>> (188 * (i % 32))) &&& dictMask else 0
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
|0=>0x1435d0d140c50d140c301147450b0c043011c245350c0530b1474e0d1404a65142db0f0804a360c045010c04e0f1405901142ca360c04a360c043014c2c301147450d140430114345010c0500f440450d440c50d3c0451f0d54f01147c3014c2051d440d101143451f28d8301383c501
|1=>0x529147450b1c2450f14343011c04529143cd090c04a75140d1031435308147450d14a45370c0450d14a45011434501
|_=>0
def opOffB : Nat → Nat → Nat
|6,0=>0x848f91e136660ca9923204388598830a608c01000
|7,0=>0xa253ca694b29251ca29432824fc9e93b2724dc9a9332624bc9692b25249c929232
|8,0=>0xb43646c0d71ac3546a0d31
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 11 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x42da055b4088280f4f01cce0399404a78086f0108e0200c03ff807ef00ede01db403a780665003ba0060000a680100000ce001980030000460002000020000380005000080000c000100000
|1=>0x101ffd1ab6a11053269a6003491b69234f2469a187fc23ff8354d
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x40000
|6,0=>0xc18711a2c524309d58e200
|7,0=>0xaa454a7954d440b4dba1899c9578a33db45f
|8,0=>0x8697e7492660
|9,0=>0xd
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 19 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_171,8,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 1 then [(dzo_41_16,4,runOps true dzo_41_16 (0,roots_41) ops)] else [])++(if pm.testBit 2 then [(dom_185,7,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 3 then [(dom_186,7,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 4 then [(dzo_171_16,6,runOps true dzo_171_16 (0,roots_171) ops)] else [])++(if pm.testBit 5 then [(dom_155,6,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 6 then [(dom_59,7,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 7 then [(dzo_169_16,5,runOps true dzo_169_16 (0,roots_169) ops)] else [])++(if pm.testBit 8 then [(dom_179,7,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 9 then [(dzo_154_1,5,runOps true dzo_154_1 (0,roots_154) ops)] else [])++(if pm.testBit 10 then [(dzo_147_8,5,runOps true dzo_147_8 (0,roots_147) ops)] else [])++(if pm.testBit 11 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])++(if pm.testBit 12 then [(dzo_179_8,6,runOps true dzo_179_8 (0,roots_179) ops)] else [])++(if pm.testBit 13 then [(dzo_178_1,5,runOps true dzo_178_1 (0,roots_178) ops)] else [])++(if pm.testBit 14 then [(dzo_43_16,5,runOps true dzo_43_16 (0,roots_43) ops)] else [])++(if pm.testBit 15 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 16 then [(dzo_186_1,6,runOps true dzo_186_1 (0,roots_186) ops)] else [])++(if pm.testBit 17 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])++(if pm.testBit 18 then [(dom_169,5,runOps true dom_169 (0,roots_169) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_187 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_171 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_41_16_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_185 _ g hchk
    · exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_171_16_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_169_16_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_179 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_154_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_147_8_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_179_8_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_178_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_43_16_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_178 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_186_1_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_146 _ g hchk
    · exact cpcs (by decide +kernel) lowS_169 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_171 8 s (0, roots_171) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_171 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_187 == dom_187) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_187 goalM v ys) : RunD true dom_187 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_187 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
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

theorem lowS_187 : Lower true dom_187 roots_187 goal_187 10 := S_187.noCircuit

def dzo_211_8:=0xf000f00000000000f000f00000000000f000f00000000000f000f00
def gzo_211_8:=0xf000f00000000000f000e00000000000f000e00000000000e000a00
def gsh_211_8:=0xf000f00000000000f000e00000000000f000e00000000000e000a
theorem lowS_zo_211_8_210:Lower true dzo_211_8 roots_211 gzo_211_8 8:=lower_iso (d1:=dom_211) (roots1:=roots_211) (T1:=gsh_211_8) [(dom_211,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_211_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a00000000000a000a00000000000a000a00000000000a000a,0,1)] (by decide +kernel) (by decide +kernel) lowS_210)
namespace S_219
def pairsG : List (Nat × Nat) := [(1,9), (1,65), (2,18), (2,66), (2,130), (3,11), (3,19), (3,67), (3,131), (8,9), (10,11), (10,26), (10,74), (10,138), (16,18), (16,80), (16,144), (17,19), (17,25), (17,81), (17,145), (24,25), (24,26), (24,88), (24,152), (64,65), (64,66), (64,80), (64,192), (72,73), (72,74), (72,88), (72,200), (128,130), (128,144), (128,192), (129,131), (129,137), (129,145), (129,193), (136,137), (136,138), (136,152), (136,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
|4=>3
|5=>24
|6=>55
|7=>20
|8=>3
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x1cf9b0cb6d037a9
|5,0=>0xe0681c189aa33a29df825969e537d8432ca3c3af390fc2f65d2a1072763a20dac1e7601bdf41b5ed128cd0de480cb6d0beb107ab7049e601a50017f8
|6,0=>0xfa6d6c3ef6c189aa92faa3e238df26666685de77587845670f55eb7547485390c45f944379b41814405d03c3af3ae363ac373875237275319ca31963302f03012e2eca22c6572a4dc28c5e22e6222d10204031c1261b25a1a6a119d2f17fd014beb128cd110fa104790f0850e0300cecd0ca780c6b608d37082f907c2007ab506fdf04f9803ef402078
|7,0=>0xcfb0cc274ea79e39e1b48641c71e81696e1695525474848a493dc5c3bef73994c281cf21ba21f6f619bd4147670e5930af1e
|8,0=>0xf8392459374337a
|9,0=>0x6f0dd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0f0f000000000f0f0000000000000c0c0c0c000000000c0c000000000000000000000000000000000000f0f0f0f0000000000000000f0f0000000000000f0f0000000000000f0f0f0f000000000f0f0000f0f0f0f0000000000000f0f000000000f0f0f0f0000000000000c0c0000f0f00000000000000000000000000000f0f0000000000000000f0f0f0f0000000000000000000000000f0f0c0c00000000000000003030303000000000303000000000000030303030000000003030000f0f0f0f000000000f0f0c0c0000000000000000000000000000000000000000000000000000000000000000f0f0f0f000000000c0c0c0cc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0000f0f0f0f0000000000000000000000000c0c0c0c0000000000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0c3030303000000000303030300000000030303030000000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000f0f0f0f000000000f0f0c0c000000000f0f0f0f000000000f0f0c0cf0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0cf0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f000030303030000000003030303000000000303000000000000030300003030303000000000000000000000000030303030000000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000000303000000000c0c0c0c0000000000000303000000000c0c0c0cc0c0f0f000000000c0c0c0c000000000c0c0f0f000000000c0c0c0c0000f0f0000000000000f0f0000000000000c0c0000000000000c0cf0f0f0f000000000f0f0000000000000f0f0c0c000000000f0f0000f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0cf0f0f0f000000000f0f0f0f00000000000000000000000000000000f0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0cf000f00000000000f000f00000000000f000f00000000000f000f00f0f0f0f000000000c0c0c0c000000000f0f0000000000000c0c0000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
|0,1=>0xf0f0f0f000000000c0c0c0c000000000f0f0c0c000000000c0c0c0c00003030000000000000303000000000000030300000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000c0c000000000000000000000000000000000000f0f0000000000000000f0f0f0f0000000000000000000000000f0f000000000000000000000000000000000000c0c0c0c0000000000000c0c000000000c0c0c0cf0f0c0c0000000000000000000000000f0f0c0c0000000000000000f0f0e0e000000000a0a0a0a000000000f0f0e0e000000000a0a0a0a00000000000000000000000000000000f0f0f0f000000000f0f0c0c0000f0f0000000000000c0c0000000000000f0f0000000000000c0cf0f0f0f0000000003030303000000000f0f0f0f0000000003030000f0f0f0f000000000000000000000000000003030000000000000000f0f0f0f000000000f0f0f0f000000000f0f0303000000000f0f0000c0c0c0c000000000c0c0c0c000000000c0c0f0f000000000c0c0c0c000000000000000000000000000000000000000000000000f0f0c0cc0c0c0c000000000c0c0c0c000000000f0f0f0f000000000c0c0c0cf0f0000000000000f0f0000000000000f0f0000000000000c0c0000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0c0cf0f0000000000000f0f0f0f000000000c0c0000000000000c0c0c0c00000000000000000000000000000000f0f0303000000000f0f0000c0c0f0f000000000c0c0f0f000000000c0c0f0f000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f00000000f0f0000000000000f0f0000000000000f0f00000000000000000000000000000000f0f0f0f0000000000000000000000000c0c0c0cf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0cf0f0f0f000000000a0a0a0a000000000f0f0e0e000000000a0a0a0af0f0f0f000000000f0f0f0f000000000f0f0c0c0000000000000000f0f0f0f000000000e0e0e0e000000000f0f0a0a000000000e0e0a0a00000000000000000000000000000000f0f0c0c000000000f0f0c0c0000000000000000f0f0c0c0000000000000000000000000f0f0c0cf0f0f0f000000000f0f0f0f000000000f0f0c0c000000000f0f0c0c3030303000000000303030300000000030303030000000003030000
|0,2=>0xf0f0f0f0000000000000000000000000f0f0000000000000000000000000000000000003030303000000000000000000003030000000000000000000000000000030300000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0c0cc0c0c0c000000000f0f0f0f000000000c0c0c0c000000000f0f0c0c0000000000000000000000000000000000003030000000000000000f0f0f0f000000000f0f0f0f0000000000000f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x423818f02007100618a01160c0a024145831e7c0800874186021418f0270d85062408824147031e04d05224019402485830264918160cb81244c5832c04905080c10124143830c0428e200c781261c5830c04291200c78100381811a3028b06185010a0c48110003830c042840608080
|1=>0x24a45831eb40920a448031e049051c2c1971e0428b063c0993c1560b063c0920a38803283c092082c18602002841c0c3010a2c1ab1e04905540c78124a428e200c781181420b06a00920a2c18f0200a8b065c78100485831e98905160c7812494583483c905463818602151100650092
|2=>0x123c0800a381861e05b05160c7816a482830c3d781241550b06580920a2c18f0249a05662c18f02482aa160c7811814710063c080242c18f0234012160d90f02482b1160c781241420b06c00920a0ca0f5e049051c2c1a71e042831e04412361570b063c0920a2c1960248290063c080
|3=>0x24828b063c092821480b063c092802c1bf1e04905423818f02482aa160c0a024145831e0491a0a2c18f0249f05160d38f02482830c3c0bd24145830c3c0bc0a2c18f3e04905202c18f024898b06e80920a2c1814048284160c09924145831ee09056e2c18f02482b7082c18f0248583
|4=>0x24145831e046920a405830c3c0920a2c1a71e04905160cb8f0248284160c3012415090160c78124145831e04012261420b06500920a2c18f024a2053a2c18f0248284160c78124782aa1c2c18f024828b063c0922a1470b063c09e0b0c5831e04905084019402485831e04925842c18f
|5=>0x5831e049051c2c18f024828b063c0923c1420b063c0920a845831e049051c2c1861e0428b8c0c7812414583283c0928a1470b06187812414884160c781
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0xa50154005
|5,0=>0x2618926231886620187a61d186e61a18626171856614184a611183e60e183260b5427608581b605580f6
|6,0=>0x2107829a0467f5df677bdde87785dda774ddcc7715dbe76dddb076a5da3667599676419897609d7b75d1d6d7599d5f7561d517529d4374f1d3574b9d277481d197449d0b74158fe73ddcf073a5ce2736dcd47335cc76301cb972c9cab729589e7
|7,0=>0xa91e9d7a59e8e8a1a27e89dde6f89a1e617969e52892a24378f1e3578b62258879e177
|8,0=>0x2b97ac9eab7
|9,0=>0x2c06
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 71 then (dictB (i / 512) (i / 32 % 16) >>> (220 * (i % 32))) &&& dictMask else 0
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
|0=>0x4e2c0c15243d464a08171e2d1c15164916152415242d1e7924174e2c284928490a3d1ea82049161516020a49286f0a3d0c2d243d0c17243d163d243d242d002f2415002f002d24151615284b1e15241528481e154e17003d24150269424808151e2d2838242d167924171c3d242d0c40243d16151655243d28480a3d0849163d
|1=>0x24151e151e2d084a1e2d16792417163d24171c15242d28481e1516492417424b08151e2d16151e151e2d0ae508481e2d424a08151e2d7815204a161520491615424808151e2d080224154e2f0c15204a0a2d2838242d0a3d003f0a491eef204816151eaa20491615223f08491e2d02e508481e2d221708491e6d242f0c2f243d
|2=>0x242d24171e2d08151e2d243d242d204b0a2d284a1e15243d242d08491e2d203f0a2d243d0a2d28491e150c17243d1e491e2d203d0a2d003f
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xf40000000000000000000000d20b2000000000092000000000063024000000002000000
|6,0=>0x6e36b36830006536230000006025d35b20005925725435224f34c34934630004424224020003d30003a30003823530000000003323122f20000002c32a22822622420000000000002131f21c31b1192163133
|7,0=>0x9729529329128f28d28b28928728528328127f27d27b2792772752732712
|8,0=>0x9b19a1991
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
|0=>0x424f72fc92204801fc7d1bc5f1745714450128400fc2d0941f0741a060120400a020050100300800
|1=>0xeff98c7e4d8fd7d5213f
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0xc0000000000045000001000009100001000
|6,0=>0x33150044c000534500514f1c411f5401414801802c01546800071470003881c11c000001815b4075c2
|7,0=>0x9d876456174a8cf8a646565959c65e
|8,0=>0x19660
|9,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_211,8,runOps true dom_211 (0,roots_211) ops)] else [])++(if pm.testBit 1 then [(dom_91,7,runOps true dom_91 (0,roots_91) ops)] else [])++(if pm.testBit 2 then [(dzo_211_8,8,runOps true dzo_211_8 (0,roots_211) ops)] else [])++(if pm.testBit 3 then [(dom_217,7,runOps true dom_217 (0,roots_217) ops)] else [])++(if pm.testBit 4 then [(dom_203,7,runOps true dom_203 (0,roots_203) ops)] else [])++(if pm.testBit 5 then [(dom_210,7,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 6 then [(dom_155,6,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 7 then [(dom_75,4,runOps true dom_75 (0,roots_75) ops)] else [])++(if pm.testBit 8 then [(dom_201,4,runOps true dom_201 (0,roots_201) ops)] else [])++(if pm.testBit 9 then [(dom_89,4,runOps true dom_89 (0,roots_89) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_219 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_211 _ g hchk
    · exact cpcs (by decide +kernel) lowS_91 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_211_8_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_217 _ g hchk
    · exact cpcs (by decide +kernel) lowS_203 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_155 _ g hchk
    · exact cpcs (by decide +kernel) lowS_75 _ g hchk
    · exact cpcs (by decide +kernel) lowS_201 _ g hchk
    · exact cpcs (by decide +kernel) lowS_89 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_211 8 s (0, roots_211) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_211 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccccccccccccccccccc, 126)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
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
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 24 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 55 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 55 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 20 0 = true)
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

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 10 := S_219.noCircuit

theorem lowS_235 : Lower true dom_235 roots_235 goal_235 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000, 1, 65)] (by decide +kernel) (by decide +kernel) lowS_171

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_242

def dzo_242_8:=0x500050005000500050005000500050005000500050005000500050005000500
def gzo_242_8:=0x500050005000500050005000500040005000500050004000500050004000000
def gsh_242_8:=0x5000500050005000500050005000400050005000500040005000500040000
theorem lowS_zo_242_8_210:Lower true dzo_242_8 roots_242 gzo_242_8 8:=lower_iso (d1:=dom_242) (roots1:=roots_242) (T1:=gsh_242_8) [(dom_242,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_242_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x5000500000000000500050000000000050005000000000005000500000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_210)
namespace S_250
def pairsG : List (Nat × Nat) := [(2,18), (2,34), (2,66), (2,130), (8,40), (10,26), (10,42), (10,74), (10,138), (16,18), (16,80), (16,144), (24,26), (24,56), (24,88), (24,152), (32,34), (32,40), (32,160), (48,50), (48,56), (48,112), (48,176), (64,66), (64,80), (64,192), (72,74), (72,88), (72,104), (72,200), (96,98), (96,104), (96,112), (96,224), (128,130), (128,144), (128,160), (128,192), (136,138), (136,152), (136,168), (136,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_250.map (· &&& dom_250)
def goalM : Nat := goal_250 &&& dom_250
def NN : Nat → Nat
|4=>3
|5=>15
|6=>35
|7=>15
|8=>3
|9=>1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0xa546973a34539e8
|5,0=>0xffaa4a01357f65d7ec0a66db14e405484c82d9c529cf4243a11f20f1ebdd171081457a00c73
|6,0=>0xee330c107dbd1e1a10119163f8aaac803567f65d7c7126c029611515e990579e74dc904bdf14b2de4aaf33a683348a32f00d2c1a52beda296e2269ba25e271d1c11312e114780f5ba0d74b0c29a090d306188056ad00613
|7,0=>0xf0997bd12bab7bc9f71d99d1c8c68364b24550613899b36f06323b731131300020efa80b6c4
|8,0=>0xbfeef69d9c35302
|9,0=>0xf38e2
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xa0a0a0a0a0a0a0a0a0a08080a0a0809414141414141414141410101414101014141414141414141414101014141010000000000000000282820202828202000000000000000002828202028282020000000000000000000050500000505000000000000000000000404000004048080a0a08080a0a08080a0a08080a0a08080a0a08080a0a080808080808080800014140000141400001414000014140000141400001414000010100000101282800002828000028280000282800002828000028280000202000002020000505000005050000050500000505000005050505050505050505040405050404a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a08080a0a08080a0a08080a0a08080000000000000001414141414141414000000000000000014141010141410100000000000000002828282828282828000000000000000020202020202020250505050505050504040404040404040505000005050000040400000404000020202020202020202020202020202020202000002020000020200000202000000000000000000014141414141414140000000000000000141400001414000000028280000282800002828000028280000202000002020000020200000202505050505050505000000000000000005050404050504040000000000000000a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a08080a0a080941414141414141414141414141414141414141414141414141400001414000282828282828282828282828282828282828282828282828000000000000000505050505050505050505050505050500000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a080808080808080901010101010101010101010101010101010101010101010101010101010101282828282828282828282828202020202828282828280000282828282020000505000005050000050500000505000005050000050500000505000005050000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a000000000000000141414141414141414141414141414141414000014140000141400001414000282828282828282820202020202020202828282828282828202020202020202505050500000000050505050000000005050505000000000505050500000000a0a0a0a0a0a0a0a0a0a00000a0a00000a0a0a0a0a0a0a0a0a0a00000a0a000140014001400140014001400140014001400140014001400140014001400140282828282828282828282828282828282020202020202020202020202020202505040405050404050504040505040405050404050504040000000000000000
|0,1=>0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a000000000000000000004040000040400000404000004040000040400000404000000000000000282828282828282828282828282828282828282828282828282820202828202505050505050505000005050000050505050505050505050000040400000404
|_,_=>0
def stPool : Nat → Nat
|0=>0x40c11720229030421208128710808a1c03043c608534418228700458808a3040c22943043ce0853043c60951c43c608b1c42020541c40c22933492022873043d20811c40c608504408a4503043ce0811c40c608b2892020471060850040c2040
|1=>0x7c808a1cc10f58808a3040c608128710808129030478808a34c1062022951c474608a1cc10f18228d1c420229c1cc10808504d10809b28730420229a1cc10214a64730460808a1cc11720228d1c40c22931cc10f20204d1c420214154c10808a
|2=>0x3045c808128730438808a3473040c808a34c1080850473043c608a1cc10808b29530458808128c10808a54d3047880811cc10808a1e230484808a1cc10808a80730458808a3045d620228c10f0c214c1032022ca3043c308a34c10808a4cd1c4
|3=>0x10808a1cc10808a3473040c808a1cc1080812873045c808a1cc1173c808a1cc10320204a1cc10808a4473043c80851cc10f20228d1cc10e2022873042022878cc1080812951cc10808a4c7
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>0x2940aa005
|5,0=>0x18d8bac57628b12d88ac3f61cb0cd85ac27610b06d82ac0f6
|6,0=>0x54de98f4579f3cdde60f29791b471e2cd0f7843c05df4ef37763b95dbced77683b25d84ebc65abab9d4eea074cba49d16e8473f31ddce0e697
|7,0=>0x709f751b28d5be91f391957c73e1a2fef778b7c5a1ec2f5a7
|8,0=>0x75dfa0fc97
|9,0=>0x1de6
|_,_=>0
def dictMask : Nat := 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 36 then (dictB (i / 512) (i / 32 % 16) >>> (251 * (i % 32))) &&& dictMask else 0
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
|0=>0x20a47292074a351cc4a1a20c5e330ca481d5c7cc3d28c571c0484a3114847291c18a313c7c829447c12328c473130a472920d87312c80c152014a312868831047cc295c70a1920c471a20c4f3420a47313cd08291cc45181ca48311874c2128d4731146072920c4c29348473134a4731
|1=>0x7312074a31286483130f482928c481d048ca3120a472920a47310cc481d20d8731047ca3128688310484a3120d47311cc481d30a47292884831047411f28c571f0484a312c7ca351cc48151ca412328c571f28648312864831
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0x79800186288000820a60000000008200011002
|6,0=>0x13ce61c938e400000452847009e9bb2000e49b1b42662c0d712c254400139a43444001010003c4708001a22e6000a9123
|7,0=>0x1b8b616a2d0598b21622c0578ae15a2b0558aa1522
|8,0=>0x1c8788f01
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 14 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 63), wireSAt ((code >>> 8) &&& 63)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 11 (j % 64)
  readOps (v &&& 15) (v >>> 4)

def pmPalB : Nat → Nat
|0=>0x9eb6ff6384ef3012fd2ef2211e70ff0fb0ef0eb0e707f06704b04904304104002e02802202001000c008006004002000
|1=>0xcefccfc4bc06
|_=>0
def pmB : Nat → Nat → Nat
|5,0=>0x1402410040c0000180044
|6,0=>0x1b3580800073075440072c118f0840803920400401c70084c0054
|7,0=>0x2381151f29e65072175a5e2
|8,0=>0x19594
|9,0=>0x14
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 6 (j % 128); fld (pmPalB (k / 32)) 12 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_242,8,runOps true dom_242 (0,roots_242) ops)] else [])++(if pm.testBit 1 then [(dom_248,7,runOps true dom_248 (0,roots_248) ops)] else [])++(if pm.testBit 2 then [(dom_122,7,runOps true dom_122 (0,roots_122) ops)] else [])++(if pm.testBit 3 then [(dom_234,7,runOps true dom_234 (0,roots_234) ops)] else [])++(if pm.testBit 4 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 5 then [(dom_186,7,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 6 then [(dzo_242_8,8,runOps true dzo_242_8 (0,roots_242) ops)] else [])++(if pm.testBit 7 then [(dom_210,7,runOps true dom_210 (0,roots_210) ops)] else [])++(if pm.testBit 8 then [(dom_184,4,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 9 then [(dom_58,4,runOps true dom_58 (0,roots_58) ops)] else [])++(if pm.testBit 10 then [(dom_106,4,runOps true dom_106 (0,roots_106) ops)] else [])++(if pm.testBit 11 then [(dom_232,4,runOps true dom_232 (0,roots_232) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_250 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_242 _ g hchk
    · exact cpcs (by decide +kernel) lowS_248 _ g hchk
    · exact cpcs (by decide +kernel) lowS_122 _ g hchk
    · exact cpcs (by decide +kernel) lowS_234 _ g hchk
    · exact cpcs (by decide +kernel) lowS_170 _ g hchk
    · exact cpcs (by decide +kernel) lowS_186 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_242_8_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_184 _ g hchk
    · exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · exact cpcs (by decide +kernel) lowS_106 _ g hchk
    · exact cpcs (by decide +kernel) lowS_232 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_242 8 s (0, roots_242) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_250 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_242 h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xcccccccccccccccccccccccccccccccc, 126)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_250 == dom_250) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_250 goalM v ys) : RunD true dom_250 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := barP true dom_250 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6 : ∀ i, 0 ≤ i → i < 35 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 35 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 3 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 0 = true)
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

theorem lowS_250 : Lower true dom_250 roots_250 goal_250 10 := S_250.noCircuit

def isoMvS_249 : List (Nat × Nat) := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_249 : Lower true dom_249 roots_249 goal_249 9 :=
  lower_iso isoMvS_249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def dzo_243_8:=0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def gzo_243_8:=0xf000f000f000f000f000f000f000e000f000f000f000e000f000f000e000a00
def gsh_243_8:=0xf000f000f000f000f000f000f000e000f000f000f000e000f000f000e000a
theorem lowS_zo_243_8_210:Lower true dzo_243_8 roots_243 gzo_243_8 9:=lower_iso (d1:=dom_243) (roots1:=roots_243) (T1:=gsh_243_8) [(dom_243,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_243_8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a,0,1),(0xf000f00000000000f000f00000000000f000f00000000000f000f00000000,0,32)] (by decide +kernel) (by decide +kernel) lowS_210)
def dzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def gzo_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0c0000
def gsh_235_16:=0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0e00000e0c
theorem lowS_zo_235_16_41:Lower true dzo_235_16 roots_235 gzo_235_16 7:=lower_iso (d1:=dom_235) (roots1:=roots_235) (T1:=gsh_235_16) [(dom_235,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (lower_slice (T:=gsh_235_16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c,0,2),(0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000,0,64),(0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,0,128)] (by decide +kernel) (by decide +kernel) lowS_41)
namespace S_251
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,65), (2,18), (2,34), (2,66), (2,130), (3,11), (3,19), (3,35), (3,67), (3,131), (8,9), (8,40), (10,11), (10,26), (10,42), (10,74), (10,138), (16,18), (16,80), (16,144), (17,19), (17,25), (17,49), (17,81), (17,145), (24,25), (24,26), (24,56), (24,88), (24,152), (32,33), (32,34), (32,40), (32,160), (48,49), (48,50), (48,56), (48,112), (48,176), (64,65), (64,66), (64,80), (64,192), (72,73), (72,74), (72,88), (72,104), (72,200), (96,97), (96,98), (96,104), (96,112), (96,224), (128,130), (128,144), (128,160), (128,192), (129,131), (129,137), (129,145), (129,161), (129,193), (136,137), (136,138), (136,152), (136,168), (136,200)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x1fffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
|8=>1
|9=>4
|10=>2
|11=>1
|_=>0
def HT : Nat → Nat → Nat
|8,0=>0x9c14c
|9,0=>0x949bf6fa3a0cfcb007c2
|10,0=>0x8ed622f7d0
|11,0=>0xcdebd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0cf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0ca0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0af0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000
|_,_=>0
def stPool : Nat → Nat
|0=>0x683910764839107683291076b8391076a83910765439107648329106543210
|_=>0
def stOffB : Nat → Nat → Nat
|8,0=>7
|9,0=>0x7e1783e078
|10,0=>0xbe278
|11,0=>0x377
|_,_=>0
def dictMask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def wireSAt (i : Nat) : Nat := if i < 12 then (dictB (i / 512) (i / 32 % 16) >>> (252 * (i % 32))) &&& dictMask else 0
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
|0=>0x21d9755f89525876258765d876259761d
|_=>0
def opOffB : Nat → Nat → Nat
|8,0=>3
|9,0=>0x92725232
|10,0=>0xc1b1
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
|0=>0x1bfeffbff5fe7fc7f800
|_=>0
def pmB : Nat → Nat → Nat
|8,0=>1
|9,0=>0x516
|10,0=>0x2b
|11,0=>1
|_,_=>0
def PM (s j : Nat) : Nat := let k := fld (pmB s (j / 128)) 3 (j % 128); fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_250,10,runOps true dom_250 (0,roots_250) ops)] else [])++(if pm.testBit 1 then [(dom_187,10,runOps true dom_187 (0,roots_187) ops)] else [])++(if pm.testBit 2 then [(dom_219,10,runOps true dom_219 (0,roots_219) ops)] else [])++(if pm.testBit 3 then [(dom_243,9,runOps true dom_243 (0,roots_243) ops)] else [])++(if pm.testBit 4 then [(dzo_243_8,9,runOps true dzo_243_8 (0,roots_243) ops)] else [])++(if pm.testBit 5 then [(dom_249,9,runOps true dom_249 (0,roots_249) ops)] else [])++(if pm.testBit 6 then [(dom_235,9,runOps true dom_235 (0,roots_235) ops)] else [])++(if pm.testBit 7 then [(dom_123,9,runOps true dom_123 (0,roots_123) ops)] else [])++(if pm.testBit 8 then [(dzo_235_16,7,runOps true dzo_235_16 (0,roots_235) ops)] else [])++(if pm.testBit 9 then [(dom_121,7,runOps true dom_121 (0,roots_121) ops)] else [])++(if pm.testBit 10 then [(dom_107,6,runOps true dom_107 (0,roots_107) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_251 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_250 _ g hchk
    · exact cpcs (by decide +kernel) lowS_187 _ g hchk
    · exact cpcs (by decide +kernel) lowS_219 _ g hchk
    · exact cpcs (by decide +kernel) lowS_243 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_243_8_210 _ g hchk
    · exact cpcs (by decide +kernel) lowS_249 _ g hchk
    · exact cpcs (by decide +kernel) lowS_235 _ g hchk
    · exact cpcs (by decide +kernel) lowS_123 _ g hchk
    · exact cpcs (by decide +kernel) lowS_zo_235_16_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_121 _ g hchk
    · exact cpcs (by decide +kernel) lowS_107 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_250 10 s (0, roots_250) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_250 h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)]]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z9 : ∀ i, 0 ≤ i → i < 4 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 4 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z10 : ∀ i, 0 ≤ i → i < 2 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 2 0 = true)
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

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 12 := S_251.noCircuit


def originalTable : Nat := 0xfffffffffffffffffffffffffffefffafffffffefffffefeffeeffeeeeccaa00
def reorderedTable : Nat := 0xfffffffffffffffffffffffffffffefcfffffffeffffeeeefffefffeeeccaa00
theorem restrictedBound : Lower true dom_255 roots_255 reorderedTable 13 :=
  lower_slice (dSub:=dom_251) (TSub:=goal_251) (rootsSub:=roots_251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(xs256.getD 2 0,32,36)] (by decide +kernel) (by decide +kernel) lowS_251
theorem lowS_255 : Lower true dom_255 roots_255 originalTable 13 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222,1),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xffffffff000000000000000000000000ffffffff00000000,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) restrictedBound
theorem goal_eq_f : ∀ r : Fin 256, originalTable.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 14 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = originalTable &&& mask256 := by
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

def witGates : List Gate := [⟨.or, [0, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [19, 20]⟩]

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

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  have hwit : (execN witGates xs256).getD 21 0 &&& mask256 = originalTable &&& mask256 := by decide +kernel
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
  have hbit : ((execN witGates xs256).getD 21 0).testBit r = originalTable.testBit r := by
    have hb := congrArg (fun v => v.testBit r) hwit
    simp only [Nat.testBit_and, mask256_bit, hlt, decide_true, Bool.and_true] at hb
    exact hb
  have hres := h2.symm.trans (hbit.trans (goal_eq_f ⟨r, hlt⟩))
  rw [hpt] at hres
  exact hres

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_51656_aux

theorem PEqualNP.Outside.L_meta_51656 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_51656_aux.main
