import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45634_aux
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
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2,hp.2] at heq; contradiction
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
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&4294967295
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
             !(isConstB d T)&&(roots.map (·&&&d)).Nodup &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs⟩,hpairs⟩:=hinit
  have hnd_xs' : (roots.map (·&&&d)).Nodup:=by simpa using hnd_xs
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
def dom_7:=0xff
def roots_7:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0]
def dom_14:=0x5555
def roots_14:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_25:=0x3030303
def roots_25:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_28:=0x11111111
def roots_28:List Nat:=[xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_38:=0x5500000055
def roots_38:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def dom_39:=0xff000000ff
def roots_39:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def dom_43:=0xf0f00000f0f
def roots_43:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_45:=0x333300003333
def roots_45:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_46:=0x555500005555
def roots_46:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_47:=0xffff0000ffff
def roots_47:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_51:=0xf000f000f000f
def roots_51:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_53:=0x33003300330033
def roots_53:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_55:=0xff00ff00ff00ff
def roots_55:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_56:=0x101010101010101
def roots_56:List Nat:=[xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_57:=0x303030303030303
def roots_57:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_58:=0x505050505050505
def roots_58:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_59:=0xf0f0f0f0f0f0f0f
def roots_59:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_60:=0x1111111111111111
def roots_60:List Nat:=[xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_61:=0x3333333333333333
def roots_61:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_7_8:=0xe8
def goal_7_16:=0xe8
def goal_14_48:=0x5440
def goal_15_0:=0xe8c8
def goal_15_16:=0xeae8
def goal_15_32:=0xeac8
def goal_15_48:=0xfeea
def goal_22_40:=0x540040
def goal_23_32:=0xea00c8
def goal_23_40:=0xfe00ea
def goal_25_36:=0x3020200
def goal_27_32:=0xe0a0a08
def goal_27_36:=0xf0e0e0c
def goal_28_1:=0x11101000
def goal_29_0:=0x22202000
def goal_29_32:=0x32222200
def goal_30_1:=0x55545444
def goal_30_32:=0x54404040
def goal_31_32:=0xfeeaeac8
def goal_38_24:=0x5400000040
def goal_39_16:=0xea000000e8
def goal_39_24:=0xfe000000ea
def goal_43_16:=0xe0a00000a08
def goal_45_16:=0x322200002220
def goal_46_16:=0x544000004040
def goal_47_16:=0xfeea0000eae8
def goal_51_8:=0xe000a000a0008
def goal_53_8:=0x32002200220020
def goal_55_8:=0xfe00ea00ea00e8
def goal_56_1:=0x101010001000000
def goal_57_0:=0x202020002000000
def goal_57_4:=0x302020002020200
def goal_58_1:=0x505050405040404
def goal_59_0:=0xe0a0a080a080808
def goal_60_1:=0x1111110011101000
def goal_61_0:=0x3222220022202000
def goal_63_0:=0xfeeaeac8eae8e8c8
namespace S_27_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(1,17),(2,3),(8,9),(10,11),(10,26),(16,17),(18,19),(18,26),(24,25),(24,26)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_27.map (· &&& dom_27)
def goalM:Nat:=goal_27_32 &&& dom_27
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x8e339dbc21bad7fd
|3,0=>0x9d277db192b669203734731c262c6e4921b3afde205d852e1c41677216a5493a1288e76e019df92000be1cca
|4,0=>0x9d277db1629e221b4dec4760464d889c3ba977c9256ff9441a9db4f605d02eb9
|5,0=>0x9d277db1
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xc000c0000a000a8080808f080f08f0a0f0aa000a0040404042020202f0f0f00f000000f0a00003030202f000f0c7070000f000300f0f0000300030000c000ca0a0a0a00f0f00f000f00c0c0c0c5050a0a
|_,_=>0
def stPool:Nat → Nat
|0=>0x71048710487104863883621c41254e2092079082471c4121c41250e2090f3090f20c4e283dcd09182090e222cea09041224e8090e43142418820
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>0xb9152264448790d216424839052064
|4,0=>0xaa94165ac6582af15bab25
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 28 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_27 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_27 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_27==dom_27) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 goalM v ys):RunD true dom_27 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_27 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27_32 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_27_32
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 6:=S_27_32.noCircuit
def isoMv_51_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)]
theorem lowS_51_8:Lower true dom_51 roots_51 goal_51_8 6:=lower_iso isoMv_51_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
namespace S_7_8
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_7.map (· &&& dom_7)
def goalM:Nat:=goal_7_8 &&& dom_7
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xd4bda944
|3,0=>0xd4bda944
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0ccaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 8 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_7 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_7 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_7==dom_7) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_7 goalM v ys):RunD true dom_7 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_7 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_7 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_7 roots_7 goal_7_8 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_7_8
theorem lowS_7_8:Lower true dom_7 roots_7 goal_7_8 4:=S_7_8.noCircuit
def isoMv_56_1:List (Nat × Nat):=[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_56_1:Lower true dom_56 roots_56 goal_56_1 4:=lower_iso isoMv_56_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
def isoMv_43_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_43_16:Lower true dom_43 roots_43 goal_43_16 6:=lower_iso isoMv_43_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
def isoMv_28_1:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_28_1:Lower true dom_28 roots_28 goal_28_1 4:=lower_iso isoMv_28_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
theorem lowS_30_1:Lower true dom_30 roots_30 goal_30_1 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x44444444,0,2)] (by decide +kernel) (by decide +kernel) lowS_28_1
def isoMv_58_1:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_58_1:Lower true dom_58 roots_58 goal_58_1 5:=lower_iso isoMv_58_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_1
def dzo_28_1:=0x22222222
def gzo_28_1_1:=0x22202000
theorem lowSh_28_1_1:Lower true dzo_28_1 roots_28 gzo_28_1_1 4:=lower_iso (d1:=dom_28) (roots1:=roots_28) (T1:=goal_28_1) [(dom_28,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_28_1
namespace S_29_0
def pairsG:List (Nat × Nat):=[(5,13),(5,21),(9,13),(9,25),(12,13),(17,21),(17,25),(20,21),(24,25),(28,29)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_29.map (· &&& dom_29)
def goalM:Nat:=goal_29_0 &&& dom_29
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_28_1,4,runOps true dzo_28_1 (0,roots_28) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_29 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_28_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_28_1 4 s (0,roots_28) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_29 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_28_1_1 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_29==dom_29) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 goalM v ys):RunD true dom_29 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_29 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_29_0
theorem lowS_29_0:Lower true dom_29 roots_29 goal_29_0 5:=S_29_0.noCircuit
def isoMv_57_0:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]
theorem lowS_57_0:Lower true dom_57 roots_57 goal_57_0 5:=lower_iso isoMv_57_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_0
def dzo_51_8:=0xf000f000f000f00
def gzo_51_8_8:=0xe000a000a000800
theorem lowSh_51_8_8:Lower true dzo_51_8 roots_51 gzo_51_8_8 6:=lower_iso (d1:=dom_51) (roots1:=roots_51) (T1:=goal_51_8) [(dom_51,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51_8
def dzo_27_32:=0xf0f0f0f00000000
def gzo_27_32_32:=0xe0a0a0800000000
theorem lowSh_27_32_32:Lower true dzo_27_32 roots_27 gzo_27_32_32 6:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_32) [(dom_27,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
def dzo_56_1:=0x202020202020202
def gzo_56_1_1:=0x202020002000000
theorem lowSh_56_1_1:Lower true dzo_56_1 roots_56 gzo_56_1_1 4:=lower_iso (d1:=dom_56) (roots1:=roots_56) (T1:=goal_56_1) [(dom_56,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_56_1
def dzo_43_16:=0xf0f00000f0f0000
def gzo_43_16_16:=0xe0a00000a080000
theorem lowSh_43_16_16:Lower true dzo_43_16 roots_43 gzo_43_16_16 6:=lower_iso (d1:=dom_43) (roots1:=roots_43) (T1:=goal_43_16) [(dom_43,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_43_16
def dzo_58_1:=0xa0a0a0a0a0a0a0a
def gzo_58_1_1:=0xa0a0a080a080808
theorem lowSh_58_1_1:Lower true dzo_58_1 roots_58 gzo_58_1_1 5:=lower_iso (d1:=dom_58) (roots1:=roots_58) (T1:=goal_58_1) [(dom_58,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_58_1
namespace S_59_0
def pairsG:List (Nat × Nat):=[(1,3),(2,3),(9,11),(9,25),(9,41),(10,11),(17,19),(17,25),(17,49),(18,19),(24,25),(26,27),(26,58),(33,35),(33,41),(33,49),(34,35),(40,41),(42,43),(42,58),(48,49),(50,51),(50,58),(56,57),(56,58)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_59.map (· &&& dom_59)
def goalM:Nat:=goal_59_0 &&& dom_59
def NN:Nat → Nat
|2=>6
|3=>100
|4=>203
|5=>325
|6=>80
|7=>10
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x53f92cd746e432bf358c239725cb91341989dcdb10632683
|3,0=>0xd4889603b92e14a485cfdfe67fab522b7dacb4317b7ecdbf78055cc16cbc652f6c1a2b92673fc83e6131223160ecb1175ea02bce5db5456c5d42859f5d1dff585bf8238e59d9b5d853826aef531cdd3e52a687ea51ecdd484ccca4db4a1d1862482af64d46699cc7456e3d5b454c6266405cdc953f6520693ab4b1b23a52ab4636820043360434de34a9747f3109c58a309777b12dcba5182d5395712b38f05829c973552797f08e27679f5026d62ccf26d5f3c925c2875a2237b59722180fae213739aa205075291fab088a1e1aa2771d1fc4f41cf6f1491c34d1f71b0af16c18d472291858053d17ce810317b783d11796d1a0170d9c80169bbc7f162050701602eaa314d5cfe5146544cb13963b6111ffa2221063132c101a4fea0f6f68690f6d379d0f5455b80eff76620dc50db30cf5578e0c94497c0c7c036d0c0619f20b1c381b0b08e41b0a751f110a1b4a7809470ac60931076f091282be0820a70f072ee59e072e934b062205de04e862f904a6ab7b04339f0e03da1cc3033fe90502edec4c0243fc1002392729015cf16b
|4,0=>0x3f52af963ec118733e9258893e8f60fa3e6b42553de78f983d1dd0df3c714b313bcbf8d73ba66e7c3b507f663a8ba7693a7b95fe39044a9338a42fe8387ea01036c734103697bcae3616055834802643344b4611336ebebf31a8c1a230f4de0b3008a6692ef3f2642ed677b32e6829be2e2a8a1d2dfb138c2dc418bb2c56791f2affeec72af4112c2ad4a3592a92278e2a30d8562a237ae929c4c05b274a3c1b273861892695948c25c1bbc2253dfbd624d81c7d24072b8223b0d832231077cc2110106b20e03d7c20ad133d201444141fcee5e01fb5a9131f56e3951f2a734e1cc2a1301cafe4541bcf7e011b7429d41b5ac44e19060e9718b4a403188c47c817d01230176d028317590e0116c6c59716aef3be156f4456145b280413ef705c131fa32d12c9985d12ab07a3129eb3cf128c5a5611fc08b210c4571c10ab6a141082376e1077b5fc1058e3ce10518f090fc975710f4553750ef8a1420ed599980e4781ff0e119acc0df755620dec9ceb0dac73920cd259170c96e0660c2ba7bf0c16583c0ba784990b0032570ac128790a652b740a5a032a0a42253f0a2a897109f8951309d41a1409825ace0800fb2f07cfb1b707c7c4c207a8b94f07951f9f071b95a806fa138006f1a070069c3d23064818130635292205d3235a0551173404987b1b03d7d871031b917602dbba7b024ba20e0115dfde00cf0b05000124e5
|4,1=>0xf59af02cebc9efc9d1dfacfdc49fa79cc336cd1dc108d4bcc0f78f82bd85a7d0b5a4f9c0b3f53575abacd06da4415410a3774aa3a2816cb69b131b3496c64e1491b411528eedfc208c6776c682ae827c828ef1f98158b9d67d3e6fd47cdbaab07cae741079487454787a4ac47838c51777a6b1507738c0cc75e79604702e09356eef5a006e7ccae46c3804396b339dd16a4de9c86a290eb86a23ebe86804f49a65c6dad66519b4d76406ac22629bd52b61b67da45e5717115dd086285ca0f26b5c1823aa5bae1f335a82a0e65a54273058be5c1058a18b9357c455fd575c6f5254a250fe50f8f6ec50768d7a4f28c3334c9587144bd7de274b1c7acb4b1299cc489e9a814866ed1444076df54385d3db436da3fc42ed3de440525997404784f54044e26140416d313f9f1f5b
|5,0=>0x1b335f401afd4d741aac4f8119cb6f2819c1a74c197d037719395797191a210518ec3f3318ccdcce181166f717f6851017f4ea4c17d2cf8b17b066eb1794f6ee178765d117060bd0170178b316d7f0e016a21180167966d71657faaa1625291d155a2ace152177b414dae23414ccdaaf1497f608144cd3f613f46ad013c6dfe513c6917213b9ee25134987761324be1a13137c3c130d9e4f12e32bc312cd2a3e12c564fd12ac062c1299c1d51274483212621f311259d1da122c30d5121b0c7611d5f30a11b4f725119ab3ba113a107f1109bebf10fef1e2107a1063106efb18105a3d3010426aab101edbcf0fed498e0f6a26170f6734580f18d8ba0eacd2040dfd0bf80dd8f06a0daecfac0da36d250d28ef470d1af1930cccd54f0c6b3ec50c46083c0c3629660bdfa30e0b88f9c70b88ded80b70506b0b0297130afdd1110ac0e4f70a7b9ec40a5a032a0a46834f09bf74d809906b9a098c191d095d4bfb0952b51a0946f19e092cab4c08ae050f088b78430859285c082bc606081e81a407f8fb7107cc46dc0763d73a07009f3b06ef289006e9aa72069412200652e2170640106b061ae90f05801c4a051a868504e6181104bb7a9a036ee3cd0365dc0c036499ab03276e3e02f685bb02da8ae802a977c4028dcdb401e8a5cf01d1ef5401c30b3e0195b712015c6f61015c1eea0106f94600ffa302005172bd0004ab3d
|5,1=>0x50d359af50a0891f504aa4a44f8252fc4f58cb294f1a4af74e7c6bb54d0805874c367cf04bd563e249f97ee1486f02de486077cf47bce8fb478f229d478a811e44b749e544ae156f43d9bf47439d5e30427de4744212dd6a41bf19de3f2468ec3f0259b83f02191a3eef82d43ea163cb3d9232613ccc02c53c54f1573ba66e7c3aec3d763acbd88d3a5f78bd39e1dfc439850f5438b4391037cc8fba379d565c37759b8837509e64373f8a8c36cd794d36352a1835c730c9354c8e3134ad79c53444e8253427fc3b34097ac133bed5c532a682db322ddae431ad116f313d8092313bef40312b962b310bad30305ed37a2fe41d792ec6004a2eadefa42e9aab212dfe6f242dad78c52da36dcf2d89581d2d4e6cda2cfd926f2c9e3f502a7caa7a2a3d07102a26b2a529ff991129e9960729d218fe29cc97ed29cc3afe29a9fe2929a4a41b28a202f42843abd1282cd0ea27ccf4d7279227fc273706e22732f29e27228e58271746eb26cbea1a26c354d9262931542621e55a253ed31a24bff3bd24ba30102433381e2351e7bf232cf9d82267f9c2213cab7a210e5e59206d93f320397d002022d7bd1ff83bf71fc06cba1fb5a9131f5e99911f3c3fea1f2e91981f0ed4eb1e56d86b1e126d901dfc70931ddb17b21d93b5391d2a055d1cc804401caa3bd41c9e22ee1c94cb5b1c93f00d1c31553a1bfe368f1be4cc591b7decc8
|5,2=>0xfe375060f3f92d19d1b7a3f9d0c67065ba3be5f9acce201fabacd06dab316071ab00f846aae0ced6a8a23d93a80e3664a5f59124a5bb8f45a1fab677a188e1759a70021199315f71991c529b8fb900788f8ae3f68dff175c8c0b90d087e0c8db8267dbbb814b1a327fd1e12c7f4ff0097d9154c97d3daa217ce86a777705d5137648edc8750ccc6072d89e57720afb0f71f2a8e06e454d366ca4d3bf6c42f4366be220206b768ded68d6a1b36828dc5067f482f76486cb94644dc43563173d666122bbf960a460555fd52c425d5f049a5ce138585b674a815b33838c5aff9abe5aa9fec35a9401485955a6125601af4f55c356f4541a585853db21e75352d1f552f4deb551fcfdf251db9f8551594c6e50ec217b
|6,0=>0xec490353d4c381b3c2e505c5bc2f8917a760e8cea6d4cf939d12b64b9a9681c19275cc058feb42498e8a03fc7ce86a777b68356a7a787fce74b1f4416dbcc28b6d7648796be220206b1f38d56a5994666902bbca6655fe545fe00cb65d22edde59687d7a58f63c6552b0e9e04eba076e4877b35f48451596480b13b7478a811e4543429c419ed0e73ea163cb3cf238573bdf02243ae318bf39760cc438c9eb16369278323145bc4d305ed37a2fe41d792b49df1824bd8a7824b172a123826cce2344c37d22810d6221af24e5204433801fb09a1a1d342a011cc804401a14885b1955abbc1928c95d18e499a0177e87ac175c50d2170178b316d7f0e016c3584c16b489bf161143ed12edf1a311fc396a10393c6a0fed498e0cb688a20afdd111098c191d0984b73607cc46dc0763d73a0564f2f4042c82b102eec5b001d05f2a
|7,0=>0xf1098be0bc640ccd6cb2dc48638b81de58f63c6543cbfcf33ce6063334c550770f0260ba0d6ebd47
|8,0=>0xf0260ba
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf000f0000000000c0c00000c0c0000f0f0f000f0f0f0030c0c0c030c0c0cf000f000f000f00c0c00000f0f000000003030c0c0c0c00f000a000a000af00000003000000f0f0f000000000000f0f0f000a0a0af0a0f0a0f0a0f0aa000a000a000a000000f0f0f0f0000f0f0f0f03000000f0f0f00000c0c00f0000000f000000c000f0000000000c0f0f0f0000000000f0f00000f0f00f0f0f0f00000000c03030c0c03030c5050a0a05050a0af0f00000f00000030c030c0c0c0c0c00f0f000f000000a0a0a0a0a0a0a0a3030c0c03030c0c00f000f0f000f00f000f000f000000c0c0c0c0c0c0c0c5050a0a0a0a0a0a
|0,1=>0xe0e00000e0e00a000f0f0f0f0000c080c08080808080000e0e00000e0e00000000f030f0cc0c0c0c08080808f0f00050f0005000070f0000070f00f0f0c0c0c0c0c0c3030f0f0f0f000000f0000000000000000f000f000000f030f000303000040c0c0c040c0c0cf0a050a0f0a050a50f0000050f0000f0e00000f000000e000e0000000000e0e00000e0e0000a080a0808080808f020f0000000000f0a000000000f0a5000f0000000000f0f00000f0f000010f010f0e000e00f00030003000300f0f0f0f08080808f0f000000000000f00030003000000f0f03030f0f0c0c30300000c0c0000f0f0c0c0f0c0c0c
|0,2=>0xf0a00000000000050505050000000000000000a0a0a0ac0c000c0c0c0c0c40c040c0c0c0c0c30003000000000000c000c0c0c0c0cf0f0f0f0f0f0000e0e0c0c0e0e0c0ca0a0a0a08080808f0f0f0f0f000f00f030f030f000f0030003000c0c0c0cf0f01010f00010070707000000000000f000a0f000a00f0a0a0a0f00000000f0f0000030300c0c0c0c0f0c0c0ce0e0c0c0c0c0c0c50505050a0a0a0af0f0f000a000000f030f0c000000000050f0f0f0f0000302030203020302e0c0e0c0c0c0c0cf0f000c000c000ce000e000e000000c0f030f00000000f0f0f0f0a0a0a0a5050a0a0f0f000000f0c0f0f000f0c
|0,3=>0xa0a0a000a0a0af0c0f0c0c0c0c0cc000c00000000001010f0f0f0f0000f0f0f00030000008070f0008070f0030303030000000000000000c0c0c0cf080f080f080000f0a0a000f000000c0808080c080808e0e000000000000f0f0f0f0c0c0c0cc0c0c0c0000000030f000f0f000f00f0f0f0f03000c00700070000000000c0f0c0f0300030000c000c000c000c00f0c0f0f000f0070700000707000000f0f0f0f00000000f000f0000000000000000f000f00f070f0000000000f000f0f0f0f00000000f000f000f00c030c03000000000000000030c030c5050000000000000000a0a0a0a0a0a80f0f00080f0f00
|0,4=>0xf0f0a000f0f0a00e0c0c0c0e0c0c0cf0f0f0f0a0000003030c0c000000003000f0003000f0000000000f0f000030303030c0c0c0c0030003000c000c50f0f0f0000000030000000f0f00000000f0f00000000f0000000f0f0000c0c0f0f00000000f000a000f000a0000f00000f0f0000f0f0a000f0f000050a0f00050a0f0000c0c0c000c0c0cf080f0808080808300030003000300e0e0e0e0000000000f000f000f0000f0a0f000f000f00c0f0c0c0c0c0c0cf0f03000300000000e0e0e000e0e0ec0f0c0f0f000f00a0a0a000a0a0a00f0f000c0f0f0c0c303020203030202c0f0f0000000000a0f0f000a0f0f00
|0,5=>0x50500000a0a0a0ac0c0c0c000c0c0cc000c0c00000c0c00303000003030010100000f0f00000000e0e0000000000a000a000a000af000a0a0f000a0aa0f0000000f00000000f0000000f00f030f000f000f00c080c080c080c08c0f0f000c0f0f0050005000f000f00300000003000000f0c0f0c0f0c0f0c00000000f0a0a0af0003000f000000303000003030000f000a000f000000a0a0a0a00000000c000f000f000f004040c0c0c0c0c0ca0a00000f000f00c0e00000e0e0000c0f00000f0f0000a0a00000a0a0000a000a0a00000a0a50500000505000050f050f0000000000a000a0a0a0a0aa0000000a000000
|0,6=>0xf0e0f000000000030f030f0f000f00c0f0c0f000000005050f0f00000000a000f000a000f00f0f0f0f0200020000e000e000e0000f0f0f0f03000300f0f03000f0f000030303030f000f00507070700000000f000f000300030000f0f0f00000000f0c0c0c0f0c0c0ce000e000e000e000000f0f00000e0000f0000000f000000000000e0e0e0e50000000f000000f0a000a000a000a00000000707000080800000f0f0000000070700000000f0e0f000f0e0f00e0000000e000000c0c030300000000303000000000000f0300000f000000f030f0c0f030f0cf0f000005050000c000f000c000f00c0c000000000000
|0,7=>0xf0303030f0000008080a0a08080a0ae0e00000e000000f03030300000000f0f03000000000030303030300030040f00000f0f0000c0c08080808080830003000f0f00001000f0001000f00c0c0c0c0f0f0c0cf030f030f0300003030c0c0f0f0c0ce0e0e0e0c0c0c0ca080a080a080a080000c0c00000c0cf0f0f0f07070000c0f00000c0f0000000030000000300e0c0c0c0f0c0c0cf0f08080f0f0808f0f0c0c0f0f0c0ce0c00000e0c00002020202020202023030303020202020000a0000000a00700070007000700e0e0e0e0e0e0e0e50a050a050a050ac000c000c000c000000f0c0f0c0f0cf000f0000000f00
|0,8=>0xb0808080b08080830f030f030f0000a0a08080a0a0808f00030000000000c0f0c0c0f0f0c0cc0c0c0c0f0c0f0cc0f0c0c000f00000000707000007005000f000f000f00c0c08080c0c0808b030a000b030a00f0a0f0a0a0a0a0aa000a000000000050a050a0a0a0a0ad0f00000f0f000030c030c030c030cf000c000f000c0030c030c000c000c0000a0a00000a0af0f08080f000800f050f050f050000f0f0a0a0f0f0a0af0f0c0c0000000050500000f0f000000f000a0f0f0a0ac0c0f0c0c0c0f0c10101000f0f0f0000c0c0c0c0c0c0cf000f0c0f0c0f0cf0000000a000000f0a0f000a0a0000a000a000a000000
|0,9=>0x80a080a080a080ae000c000e000c00b0b08080b0b0808f0100000f010000302020203020202c0000000c000000000030300000000f0a0f000f0a0f00a0a0f0f0000000030f030f0000000030000000f000000f000f0c00000c0cf0404040f0404043030f0f00000000f0f0a0a0a0a0a0ac0c0f0c0c0c0c0cf0a0a0a0000000000e000e000e000e80a080a0a0a0a0ab0b0a0a03030000a0000000f000000c000c000f000f005000f0f00000000e0c0c0c0c0c0c0cf0f0c0c0f000c0000c0f0c0f0c0f0cf0f0a0a0f000a00c0000000f000000606060606060606a0a00000000000080808080808080850f00000f0f0000
|0,10=>0xf000f0f0f000000f0500000f050000302030202020202000030003000300700050007000500f0f03000f0f030000000000f0f080830f0000030f0000202000002020000a0f00000a0f00005000f0005000f00a0f0a0f000000000000f0000000000f00000000000000f0f000a000a000a80808080a0a0a0ac000f0000000f00f0c0f000c0c0000f080f080f080f08f000f0008000800200020002000200f0a000a0f0a000af0a00000a0a000050005000500050000a0a0a000000002000a0a02000a0a0000c0c0f0f0c0c80008000f000f00707070700000000f0f0e0e0f0f0000c0c0f0c00000f00b0b00000b0b0000
|0,11=>0xf0300000f030000c0c0f0f0c0c0c0c500050000000000f000f000c000c00700000007000000f0a0f0a00000000f05000005050000f0f0a0a00000000202000000000000a0f00000f0f0000f0f0f0f0f000000a0000000a0a0a0ab000b0000000000c0f0c0f0c0c0c0c4040f0f00000000e0c0e0c0e0c0e0c404040404040404f0f0f0f04040404c0e0c0e0c0e0c0ef0c00000f0c000000000000f0a0f0ad0f0d0f0c0c0c0c0000f0a0f0a0f0a00e000e00000000a0a0a0a000a000a1030103000000008000a0008000a00f0f0f0f000e000e10f0000010f0000f000c0000000000f0c00000c0c000000a000a00000000
|0,12=>0xf0a0a0a0f0a0a0a00000000f000000500000005000000f050f0005050000300000000000000a00000000000000f0c0c0c0c0c0c0cf0f0f000f0f000000a0a0a0a0a0a0ac0c0f0c0f0c0f0cb0b0b0b00000000f0f0a000a000a00f00000005000000d000d000f000f000020002020202021010f0f00000000000000002020202c0e0e0e0c0e0e0e30f00000f0f0000f0c0f000f0c0f00
|_,_=>0
def stPool:Nat → Nat
|0=>0x28d802051a8d01033008142c0f028c81631008c05e2e00814161b168b0221b02810560f00814541b00814360d028101001028a450010289c4c01028484a0102830482300814441b02884401f0f014161d02870361a0286402050c0482c17008142c0102854280109848220102830200f008141001070141a0102830160a028041203040140e01028180a04018080200
|1=>0x280c50052d80c10052d164b01b00800481b2b958aa1f0281050540294ca41f008141e01029445001029402c4f00814160102938164d02830501b2612c940f00814921b0281036010292036052384850460280c8a0200814484400814364302810841b009045001029001601028fc3601028f8101f1e8140205018f03605020ec2c0f1d014721f008141601028e06e1b
|2=>0x2e0141e81008141601401fc107e3e8143601029f0f60f008141601029e80a79061e0487700814167600814167502830aa1f00824047400814e67202830163a028305001029c4e01b028101001029bc506e029b45001029b002053580c3a01029a80a04349a0ce0f00814cc010299450640298c040131184160102980be02008143e0f26014025e06174480226014505c
|3=>0xd80548a31406c02a25082d3e1b4f0153a1b00814600b0e8040a860586c0a044e02c6e1b16814160102a6d221f00814609a1406c0a994c0a036054b8c8360102a592a1b4a24c020505a48020548955201f008141628008151e280d8340a8e058a11a05460a1160102a291201028484802440150e1b008142c0102a18508502964160f3aa1106010280c101f02a08101f
|4=>0x29bc161b5c0054a0b00adc0ab6058a03e9e0282d6a010d01416285a014ca0b07acc02050b0a0020559154161b02810161d02ac51c243f06c0aad2c0900a8c3682d600f2b8143a0f008155e0b142240aa905ab802055682c020535a2848ac00815560b1400554050594836010282c501b02870b0240d81552280d8040aa80586d4e010282cfc1b53014101f008154a0b
|5=>0x1406c02056a8a1a80102b4c2cd2078040a0b688040ad0008159eb66702c3a0102b341628660040a1b008152acb0d8040aca6482d90c700814161b63014080b0d81408c505b1002050982d861b02810501b0092d64c20f83c02050582002c102890040160014501b00aad7e0b00815620c058741ebe029cc501b5e814160f00815781b0081576ba1200802055c9545001
|6=>0xda4c0a280d9b802052a8a0fc7d0282c3a0f02b9c1614008c1cc0b040040ae50a06c02050916048d100814162812005c60b143880ae10b06c5a010282dc001028c1be1b168040a551407c8c052a87d4c01028a03e0102b781edd008152a0b3f06c5a050d80434056e02c02056da44aa1f00814780b1406d3c056d0a03e010282c500102b65b0d70d8040a280f8040ad6
|7=>0x7f02d880102968161b7e8040a287e06c02057d83c0205460a0fc1f02be8161b00815f2285a814f278122c0040102960481b7c014501b00815ee0b00815eccf0586dea05358dc3e0f0081448f40d8040a0b0d815e6ad058a036f2788203e0102bc1de240d8040a0b77014daed05a4036460282c501b76014b0450d8040a557587c020505ba836e9028a0360d02ba06e28
|8=>0xd9700a91848a036f2028a0364602a88aa28170040a550f8040a6b14004e40501960360131184360102b721055140040b07128a03706028a0360102c14161b02810d0280d8040a6a758040a693402c500546410aad70f8040a1607804e4052c092060102892021b0081450aa029e4f00b0ec0802052a8a2020102890360102c0048ff0d8040a24010043c05058a03657
|9=>0x2b148416078040a0b141300b170d8040a130906c020565254aa280fc580a421406c8cab2c0040a353296048b071014161d079340a0b078062a051203c020550ac1c4054aa6816280d80624280f8040afa0586e22010282c50dd02c40481f878040a0b140161c8c140040a038682e181b00814490b0d8040a0b0d8b53c052ac283e015282da40102831b02802968da0b
|10=>0x928a03e010282c3a019201416280d87e461f078040b221406c1a059082c360102c803601029b42428009f40a0305875fe01028a002056999416280dc7c0aea140040a030586c3e0502090360102c78481b00aae3a551447002050586e361e02ba8481b8d014e6280dc640a0b009c80a0c0586c02058c07c1e0102b143a0f00978ba581209802050da4c021a028900401
|11=>0x2b3ce6240d8040aa5058a00a8c4702c360102c212a0b6906c02054a82c501f008165c9d1406c02050982c501b008165a0b1406c032c0282c501b0081656280f8040a134d02c3a2800ca80a73058741e010282c501b4f0040a0b1403c02055102c5001029699e0b0d8040aa55b02c501b00816520b1406e5005938a03e010282c501b720b01628230159e0b140040b26
|12=>0x1206df005058a1a41b0f014161d078067405058a0360189a84161b008680b394e8a0360102a801738078040aa52a82c3601028f016280d8066e05058a0360102a88161b168040a95058a11a1b0081416280d8040b35058a2681b0081416289986c0205058a036dd02c8416ea0f83c02051406c0205991a017311406c02ab058a0361f9801416289786c0205058a002c1
|13=>0x5025416285806cae05058a0374100814161b00d000a95058a02801098c0501b458040a950586cae0102a54161b00814fe95058a0373f463a016280d8040ae1058a0373e0081416280d8040a86058a036019501416280f80426a1058a0373d02ab4162800aa80a0b144f0020597090360102ad8ba280f83c02055582c360f008155a0b0d87c02059002c501b02cec1628
|14=>0xb040a68398a0360102994501b009c80ad3058a0360558a381628a503c020505d24361f0081416281240c02050583c02055284c162800815b6cf0586c02056e2d816240da500205058a0360102d1c501b078040aaf1406c3e0102aac50240f8040ab9058a0360102d181628120040b2e05890360102d14501b008168943a10a0368b008144a280d8040ab60586c0205
|15=>0x58a03601a7814161b0f8155af0058a0360f5f01416280d80690a1058a29c1b0081416280f816428c14308361f008141628122240205058a29a1f00814b0240d805c405058a2281b00c4c16287e06c02051206c02053cad850b00f8040a5d128a0374c0081416280f8040b4b058741e01029e016282a0040a5a058a0481b26014161b008154b081206c3e0102a441628
|16=>0x2ab4160f008155ab90586c020548bc1b0280f8040a8c0586c0205ac2d816280d805fd570586c035602a54501b008142697058a1600102d54501b0f806a805058a0be1b0081416280d8040a962a8a03e0102d4c16371406c0a8c0586c020535a5416280dd48020505ba8360f0081417511406c02050586d820556bc0501b0f8040b502a82dd61b0081416288a07c0213
|17=>0xe83c021e0282ebe1b078040a0b1257836010282c514d02a3016280d87c0b5d058a0360102d7016280d80557501406c02055025c16280d8040b5b058a0360102a4416370d83c020505d68360102ab416280d8040acd05bac360102d6450b00f8040a79058dc501b029e416280d804c461058a0360109a84162800ca80ab91406c3e0102b4c16280081690650586ddc01
|18=>0x2da016ea0dbb802052c090360102ae450240d8040b670583c020552a3016280d8040b66058a0360102d941628490040a132a82c362d0081450240d806a805b202c500102cb816280d9300aab0586c1e0556a38481b078040a68058a0fc1f02a301628688040b63058a0376200814501f0081556b9058a0494d008141628b086c0205058a0369e0282c500102acac00b
|19=>0x1406c3e01028a25e1b0081416280081522b9058a0371a008141628078040b13058a03f6d00814161ba90040a912a8a0368b008141628b607c0205058a002053499450240d8040b6b058a036a60081416280dda80205058a00205729a016280d8040b690586c3e0151c34501b029e58a781406c3e053cba01628008151869058a2a40102ae4161b008155ad31406d1601
|20=>0x1406c03730282c501b008380a0b1400582050982c50d100815340b1403dba0102890360102a952a111406c02054602c3601608152a280d83402054602c500fb90040a0b0d81408581406c0205510a03e0102aad640b1406c0a32058a0360102c8816280d8040b360586c02055299416285807dc405058a0360f02b9c16280d8040b71988a036015582c501bb8016976e
|21=>0xd8040a0b1406c0aa55482c50d20d816df781406c3e010282c50d20d8040a0b0d8040a3c3402c501b00816ee731406ce405678a1f81b008141628122c1c405058a03601bb01416280d9d40a0b1406ce80102dd4501f078040a0b1b8a036e20282c501b00816e80b1406c0b212d02c50d1170040a0b1406c0ac5740a0360102c89b80b1407c02053f82c360102a46a60b
|22=>0xd83c1a010282c50b0a90040a0b752c01e010282c501b95015d00b1b8a036c00282c500102b96f6551407c0205be82c517c078040a0b1406c3ee49082c5024130040a581b89036010282c360102c219e0b1406c0a8c2c82c501b00814fe0b141f836052d02c501b00816f60b1406c02058b8a2f41b0f8040a0b1409028010982c50330d8040a421406c02056982c5179
|23=>0x8158a0b1406e46240d83c02053c82c3a0f00815620b1434836e40282c500f0081536280d8040adc2eb60501b00815560b1406c02b702960161b00814d65505ba8361e0282c501bc10040a0b1406c0205c082c497f0d8040a0b146003e01029cc481b008156c0bbf86c1e0102844501b078040a0b1406c8c058982c501bbf1c80a0b1407c02054d8a03693008158a28
|24=>0x1406f1401028a0361f00e240a0b1407c02055c82efe1b008155a0b1406c0a794702c501f00815ca0bc40a036010282c501bc38040a55850a03e010282c501bc30040a240d87c1e010282c501b008170a0b1406c02052d02c501b0081708240da4c0205568a0361f00aacba0b1403c02c1028a0361f0081706280d8040adc3c82c501bb8015180b1406c0b132d82c360f
|25=>0x816400b146343601028a0361f458040a280d87c02052b02dae1b00814b4280d8040aaf058a0361fb7ba0161b0f8b40205058a03601028b0178c0dd480205058a0481b5a014501b0fbc80205058a0360f028c816830d8040a0b1406c2e01028a0375200814f20b0da9802052d02c501b0081716240d8040a795682c502400815ca281206c02056e02c501b00815940b
|26=>0x5282c501b790040a0b1406c02055284c16280d8040aa5ab8a0361f00815560b1406c1e019d01416280d80654050586c1e0102ab416280d8040a8e058a036019b81416280d8040aa23982c501b078040a0b1406c1e0102ab416280d83c0205c882c501f008159e240f83c0205058a3201b00814aa280f8040aa5058a0360102e3c501ba90040aab058a0360102e38161b
|27=>0x2c85180b1406c0205a582c501b078043c05058a03601390152b75058a0360f0081416280d805c4054d02c501b00814c40b1406c1e0102a6816280d8040a91058a0361f00816420b1406c020555ac816371409036010282c501b0f8043c05058a0360102a95400b140040ae5058a037520081416ea0d83c0205058a0360102aad5a0b1406c1e01029e016280d95c0205
|28=>0x2a3016280d8040a6b058a0361f00816de0b1406c03400282c501bb7ba0161b168040a0b1406c02053f82c501b078040aa5058a03601029e58a0b1434836010282c501b0f8040a59058a2281b0f8040a0b1406c3e0102a9416eb0d8040a731406ce405058a0360f00817240b1406c3e0102a8416280d8040b22058a0360102cd8161b00814780b1406d16010282c501b
|29=>0xd81518e8058a0361f00816900b1406c3e0102ba016280d8058005058a0361f00816260b1407c02055c96016280d805c405058a0361f00815220b1406c3f52008141628c986c0205058a0360102a32960b1406c02052d02c501b0fb900205058a0360102cfc16281205036010282c501f078040a0b1406c02057f2b416281206c02056282c501b00ca80a79058a03601
|30=>0x16280d8040a0b1406c0205b782c501b00816420b1406c3e010282c501b009c80a0b1406c02054602c501b00814260b1406c0205a402c501b00815d00b1406c0205058a036e40081416280db92420b1406c3e0f0081416281206c02054602c501b078040a5d058a03601029e5180b14090360102d201628
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xf300c30093006300330003
|3,0=>0x10e410a4106410240fe40fa40f640f240ee40ea40e640e240de40da40d640d240ce40ca40c640c240be40ba40b640b240ae40aa40a640a2409e409a40964092408e408a40864082407e407a40764072406e406a40664062405e405a40564052404e404a40464042403e403a40364032402e402a40264022401e401a401640124
|3,1=>0x19e419a41964192418e418a41864182417e417a41764172416e416a41664162415e415a41564152414e414a41464142413e413a41364132412e412a41264122411e411a411641124
|4,0=>0x2dd52d852d352ce52c952c452bf52ba52b552b052ab52a652a1529c52975292528d52885283527e52795274526f526a52655260525b52565251524c52475242523d52385233522e52295224521f521a52155210520b5206520151fc51f751f251ed51e851e351de51d951d451cf51ca51c551c051bb51b651b151ac51a751a25
|4,1=>0x41d54185413540e5409540453ff53fa53f553f053eb53e653e153dc53d753d253cd53c853c353be53b953b453af53aa53a553a0539b53965391538c53875382537d53785373536e53695364535f535a53555350534b53465341533c53375332532d53285323531e53195314530f530a5305530052fb52f652f152ec52e752e25
|4,2=>0x55d55585553554e55495544553f553a55355530552b55265521551c55175512550d5508550354fe54f954f454ef54ea54e554e054db54d654d154cc54c754c254bd54b854b354ae54a954a4549f549a54955490548b54865481547c54775472546d54685463545e54595454544f544a54455440543b54365431542c542754225
|4,3=>0x594558f558a55855580557b55765571556c556755625
|5,0=>0x710670a670466fe66f866f266ec66e666e066da66d466ce66c866c266bc66b666b066aa66a5569f66996693668d66876682567c66766670666a6664665e66586652664c66466640663a6634662e66286622661c66166610660a660465fe65f865f355ed65e765e165db65d565cf65c965c365bd65b765b165ab65a5659f65996
|5,1=>0x890688a6884687e68786872686c68666860685a6854684e68486842683c68366830682a6824681e68186812680c6806680067fa67f467ee67e867e267dc67d667d067ca67c467be67b867b267ac67a667a0679a6794678e67886782677c67766770676a6764675e67586752674c67466740673a6734672e67286722671c67166
|5,2=>0xa0c6a075a0169fb69f659f069ea69e469de69d869d269cc69c669c069ba69b469ae69a869a2699c69966990698a6984697e69786972696c69666960695a6954694e69486942693c69366930692a6924691e69186912690c6907590168fb68f568ef68ea58e468de68d868d268cc68c668c068ba68b468ae68a868a2689c68966
|5,3=>0xb876b816b7b6b756b6f6b696b636b5d6b576b516b4b6b456b3f6b396b336b2d6b276b216b1b6b156b0f6b096b036afd6af76af16aeb6ae56adf6ad96ad36ace5ac86ac26abd5ab76ab16aab6aa56a9f6a996a936a8d6a876a816a7b6a756a6f6a696a636a5d6a576a516a4b6a456a414a3b6a356a305a2a6a246a1e6a186a126
|5,4=>0xd026cfd5cf76cf16ceb6ce56ce05cda6cd46cce6cc86cc26cbc6cb66cb15cab6ca56c9f6c996c936c8d6c876c816c7b6c756c6f6c696c636c5d6c576c516c4b6c456c3f6c396c336c2d6c276c216c1b6c156c0f6c096c036bfd6bf94bf36bed6be76be16bdb6bd56bcf6bc96bc36bbd6bb76bb16bab6ba56b9f6b996b936b8d6
|5,5=>0xd205d1a6d146d0e6d086
|6,0=>0xeb97eb36eac7ea66e9f7e996e927e8b7e847e7e6e786e717e6b6e665e615e5b6e547e4d7e476e407e397e327e2d5e285e217e1a7e146e0e6e095e036dfd6df76df07de97de27ddb7dd56dce7dc86dc17dba7db37dac7da57da05d9a6d946d8d7d867d7f7d796d727d6b7d656d5e7d586d526d4c6d466d406d397d327d2b7d256
|6,1=>0xf255f1e7f177f107f097f027efc6ef57eee7ee86ee17edb6ed47ecd7ec67ec06
|7,0=>0xf5f6f596f536f4d6f476f416f3b6f356f305f2a6
|8,0=>0xf655
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 404 then fld (dictB (i / 512) (i / 32 % 16)) 60 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x1406c00814144d8140060586c058051406c142330d8141406c078061406c0d8070586e0d81405b920081505a811404c0d814058a01406c140050d81414005058a11401572487008150081414014140050d8141406c0d8140d8050d8048a44f0f8140f815058050580614230140161406c0d8140d8140586c0d8070db900081514006008140db90008150f804058a005816058a10f80700a810d814142330d807
|1=>0x140161407e1406c0f816058161406c05c85008140586d0d8040f8140f8150586f0d80705805058160dc85008141406c140061404f140140d8140583f1406c05816144500f8151406c140140d814058a2145231407e058161406c058a005816058050586e0f8141406c0586f0586e0084d0d81402a330d807140050084d0d8140fb92008151406c00815058160586c1444f0f8140586c0f8160db90008150fc85
|2=>0x1407f1407c0db90008151406c058a31407f1406f140151406c0d8050d80702b3f1406c1404f142330d8140d81700815058a0058a21406c1406c05814058161406c0dc8500814058a2140161406c008148a0070f8150084e0d8141404c0d8140f80505a310d8070dc85008141406c142300d8070f8161407c05a33140070d8071406c02a3302a3005a831404c1404f0f8171406c140151407e058070f8050f805
|3=>0x1404c00a550d804058a00d9cb0d80414233058051406c0dc87008140f81700815008141404f0d8140f8060f8050f81512231058a00d8071404c140151452c008161406e1406c05804140051406c1407d058040f8050db9000815142301404f0f8161406c0dd000ddbf008170d807142330db90008150d8070d81400b3d1404f0d8141404f0f8161406c140051406c00d2d0081605dbd008171406c0d8141406c
|4=>0x1406c058a01406c058a0058a01404c1406c00815058051406c00817008160586c0f8051406c0583c1407d140150586c0084d140061406c0d8070586c0586c1404f0d8140d9af1406c0081705c520f8151406c0f8061406c1406c058a00d814058a114015058a00d8070da2f1406c0d8071423305ba2008161404f00d2d02a307248700815008140586c1404f0d81405ab50f8161406c140061406c058050f806
|5=>0xd9cb0d8040db92008150db90008150d807008140dba0008160586c0586f0d8041407d1406c1406e0d8040f8171406c058a31407f1406c1406c008141404f0f8051406c1406c0d8041404c0d8140dc87008141407c1406c058051406c0d807140061406c0d8140084d0d814140140d8140d8141406c1406c142330d8071406c0d8070f8061406c145230d8171404f0d814140051406c058071406c1406c058a2
|6=>0xd807058a00d8170d80700816058171406c1406c008160f8041406c0f8141406c058161406c0d8041407f1406c1407c0f8151406c02a300d807142300d8071406c0081502a330d807140151406c02a330d8071406c142330dc87008141406c008170ddbf0081700817008160f8161406c058141406c0d8070f8051406c0f8061406c0f8151406c058a00d8140dc85008140d8041407e1406c0f8161406c1404c
|7=>0x817008141406c0d8040d8070d8140d81700816008150081500814058a01406c058a00d807140161406c14007
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0x1880000000000000000000000000000000000000000000000000108000000000000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000100000000000000000000000
|4,1=>0x111079000000000000000000000000000000000000000034800000000000000000c100000000000000000000000000000000000000000002c4000092000000000000000000000000810000000000000000000000000000000000000000000000000000
|4,2=>0x8040000000f100000000000000000000000000000000000000000003a2000000000000000000000000001b20c180000000000b88548282000000000000000000000000000000000000000000000000000000000000000000000000000000122
|4,3=>0x4e200000000004a40001118844000000
|5,0=>0xb0256200000000000002a8948c0005022789348964000250800000049124080008e24520000000882000218800000000000000000004121f18f447820000000e8800039100000007023621998c480002f216180000002b115080005220001408000000000
|5,1=>0x24040008d346080000000004510001104871429210400083140900000008013f8800000000000000000007d23e080000007a20001e08ec47420001c88e046e23689b0400000034999c80000000000000cc2642000184cbe40002f080000005c22d10000000591
|5,2=>0x31c58a4c326108000000c11600af89784bb15c900000000005c0adc40000005b080000000000002d08000b31590ac45602af10002b855a20000002a8d522000000298d4840000000000000a3150928053c40004e126880000004c8a5c80009524a0a488000911
|5,3=>0x7d1be440000007b90000000f527a08001e440000003c09de20007708000000ed10003a8c0000007488001d020000003989ca2e417110001c22000700b7880000006e136c5b42d82000354da82d3168934059e200000000019c200066132c4000c920000001902000
|5,4=>0x9d080000013829b10000001342998cc4a5e52e196100000012a20004a44001281000494e482000911480a3e31d28e0c68800118200045c40011618a8c4c800112188143c61a4000000428c00000000042460e5061000000000104200040880010118008001fe2fd2
|5,5=>0x13d20004f040013b1
|6,0=>0xd4969cb4a5a32d10e8473e59e1ce88003365992cb96548001932c8964071c58c2c51620b0c5851c19604b0037e2be15e8af05762ba8dccae256f2b695b06d45682b38d94ac65612af9574ab655a1ac155c6aa5532a90d446a034e2a61528a905462a21508a8233f2
|6,1=>0xe39714b865c12df96f4b765b92db96d4b665b12d80eb8b5a3ab2
|7,0=>0x3a23d01e78f3879a3cc1e58f284001c91
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xa269238a181f71b6995d55134503cc2ca2481c61440c2040
|1=>0xffbe75cf0bedb2baa9
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x2200000000000000000008000200001000000000000000000001002000000000001000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000008000000000000080000000000
|4,1=>0x40000040041000000000001000180000000001000000000080000000000008040000201040200000000000000000000000000000001002
|5,0=>0x10091400011400443c100104000104004000000204000300120100804210100024a00000004101404024000f04000800064200000038602604824039900120068100064004000000000269924000800e000046908001240004080040208000
|5,1=>0x6c100068000804804020204004000100300010024000165d0409800410006c404201f20408820000020408101a00004001114144000818108204800064100010000000820814e64800804000b64000f0800000090c10401c200005f008683001
|5,2=>0xb00100e10000514000110b24114020200801900964068164265500100100838200104468004d00001a08400000b003048040102
|6,0=>0xa8b2cb716a101683d324b26ba0c4ab24b5d9681adaaa546250859a3cb8de09016b5eba2b6a12e1a09a5a3e1809ae790c2ddac975266592b6182e038b
|7,0=>0xaab2e595862baeb
|8,0=>0xb
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 6 (j % 128);fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_51_8,6,runOps true dzo_51_8 (0,roots_51) ops)] else [])++(if pm.testBit 1 then [(dzo_27_32,6,runOps true dzo_27_32 (0,roots_27) ops)] else [])++(if pm.testBit 2 then [(dzo_56_1,4,runOps true dzo_56_1 (0,roots_56) ops)] else [])++(if pm.testBit 3 then [(dzo_43_16,6,runOps true dzo_43_16 (0,roots_43) ops)] else [])++(if pm.testBit 4 then [(dzo_58_1,5,runOps true dzo_58_1 (0,roots_58) ops)] else [])++(if pm.testBit 5 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_59 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_51_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_56_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_43_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_58_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57_0 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_51_8 6 s (0,roots_51) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_59 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_51_8_8 h
def symsG:List (List (Nat × Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_59==dom_59) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_59 goalM v ys):RunD true dom_59 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 6 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 6 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_0:∀ i,0 ≤ i → i < 64 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_64:∀ i,64 ≤ i → i < 100 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 36 64=true)
private theorem z3:∀ i,0 ≤ i → i < 100 → Z 3 i=true:=(range_split z3_0 z3_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 203 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 11 192=true)
private theorem z4:∀ i,0 ≤ i → i < 203 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 z4_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 320 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 256=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_320:∀ i,320 ≤ i → i < 325 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 5 320=true)
private theorem z5:∀ i,0 ≤ i → i < 325 → Z 5 i=true:=(range_split (range_split z5_0 (range_split z5_64 z5_128)) (range_split z5_192 (range_split z5_256 z5_320)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 80 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 16 64=true)
private theorem z6:∀ i,0 ≤ i → i < 80 → Z 6 i=true:=(range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 10 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 10 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_59 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_59 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_59 roots_59 goal_59_0 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_59_0
theorem lowS_59_0:Lower true dom_59 roots_59 goal_59_0 9:=S_59_0.noCircuit
def isoMv_53_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_53_8:Lower true dom_53 roots_53 goal_53_8 6:=lower_iso isoMv_53_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
theorem lowS_60_1:Lower true dom_60 roots_60 goal_60_1 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x1010101010101010,8,12)] (by decide +kernel) (by decide +kernel) lowS_56_1
def dzo_7_8:=0xff00
def gzo_7_8_8:=0xe800
theorem lowSh_7_8_8:Lower true dzo_7_8 roots_7 gzo_7_8_8 4:=lower_iso (d1:=dom_7) (roots1:=roots_7) (T1:=goal_7_8) [(dom_7,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
namespace S_15_0
def pairsG:List (Nat × Nat):=[(1,3),(2,3),(2,6),(4,6),(5,7),(5,13),(9,11),(9,13),(10,11),(10,14),(12,13),(12,14)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_0 &&& dom_15
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_7_8,4,runOps true dzo_7_8 (0,roots_7) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_7_8_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_7_8 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_7_8_8 h
def symsG:List (List (Nat × Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_0
theorem lowS_15_0:Lower true dom_15 roots_15 goal_15_0 5:=S_15_0.noCircuit
def isoMv_57_4:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_57_4:Lower true dom_57 roots_57 goal_57_4 5:=lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_0
def isoMv_45_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_45_16:Lower true dom_45 roots_45 goal_45_16 6:=lower_iso isoMv_45_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
def isoMv_29_32:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 5:=lower_iso isoMv_29_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_0
def dzo_53_8:=0x3300330033003300
def gzo_53_8_8:=0x3200220022002000
theorem lowSh_53_8_8:Lower true dzo_53_8 roots_53 gzo_53_8_8 6:=lower_iso (d1:=dom_53) (roots1:=roots_53) (T1:=goal_53_8) [(dom_53,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53_8
def dzo_60_1:=0x2222222222222222
def gzo_60_1_1:=0x2222220022202000
theorem lowSh_60_1_1:Lower true dzo_60_1 roots_60 gzo_60_1_1 5:=lower_iso (d1:=dom_60) (roots1:=roots_60) (T1:=goal_60_1) [(dom_60,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_60_1
def dzo_57_4:=0x3030303030303030
def gzo_57_4_4:=0x3020200020202000
theorem lowSh_57_4_4:Lower true dzo_57_4 roots_57 gzo_57_4_4 5:=lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_4) [(dom_57,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_57_4
def dzo_45_16:=0x3333000033330000
def gzo_45_16_16:=0x3222000022200000
theorem lowSh_45_16_16:Lower true dzo_45_16 roots_45 gzo_45_16_16 6:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=goal_45_16) [(dom_45,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_16
def dzo_29_32:=0x3333333300000000
def gzo_29_32_32:=0x3222220000000000
theorem lowSh_29_32_32:Lower true dzo_29_32 roots_29 gzo_29_32_32 5:=lower_iso (d1:=dom_29) (roots1:=roots_29) (T1:=goal_29_32) [(dom_29,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
namespace S_61_0
def pairsG:List (Nat × Nat):=[(5,13),(5,21),(9,13),(9,25),(9,41),(12,13),(17,21),(17,25),(17,49),(20,21),(24,25),(28,29),(28,60),(33,41),(33,49),(37,45),(37,53),(40,41),(44,45),(44,60),(48,49),(52,53),(52,60),(56,57),(56,60)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_61.map (· &&& dom_61)
def goalM:Nat:=goal_61_0 &&& dom_61
def NN:Nat → Nat
|7=>1
|_=>0
def HT:Nat → Nat → Nat
|7,0=>0x653667d8
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x3333333300000000cccc0000cccc0003300330033003300c0c0c0c0c0c0c0c2222222222222222
|_,_=>0
def stPool:Nat → Nat
|0=>0x4688
|_=>0
def stOffB:Nat → Nat → Nat
|7,0=>5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 5 then fld (dictB (i / 512) (i / 32 % 16)) 62 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 3 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 8 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 7),wireSAt ((code >>> 5) &&& 7))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x3f80
|_=>0
def pmB:Nat → Nat → Nat
|7,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 7 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_53_8,6,runOps true dzo_53_8 (0,roots_53) ops)] else [])++(if pm.testBit 1 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 2 then [(dzo_60_1,5,runOps true dzo_60_1 (0,roots_60) ops)] else [])++(if pm.testBit 3 then [(dzo_57_4,5,runOps true dzo_57_4 (0,roots_57) ops)] else [])++(if pm.testBit 4 then [(dzo_45_16,6,runOps true dzo_45_16 (0,roots_45) ops)] else [])++(if pm.testBit 5 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 6 then [(dzo_29_32,5,runOps true dzo_29_32 (0,roots_29) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_61 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_53_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_60_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_57_4_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_45_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_29_32_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_53_8 6 s (0,roots_53) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_61 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_53_8_8 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_61==dom_61) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 goalM v ys):RunD true dom_61 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
private theorem z5:∀ i,0 ≤ i → i < 0 → Z 5 i=true:=by omega
private theorem z6:∀ i,0 ≤ i → i < 0 → Z 6 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 1 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 7):∀ i < NN s,bar true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_61 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 7) (h:RunD true dom_61 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_61 roots_61 goal_61_0 8:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_61_0
theorem lowS_61_0:Lower true dom_61 roots_61 goal_61_0 8:=S_61_0.noCircuit
def isoMv_7_16:List (Nat × Nat):=[]
theorem lowS_7_16:Lower true dom_7 roots_7 goal_7_16 4:=lower_iso isoMv_7_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
def isoMv_38_24:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_38_24:Lower true dom_38 roots_38 goal_38_24 4:=lower_iso isoMv_38_24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
def isoMv_14_48:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_14_48:Lower true dom_14 roots_14 goal_14_48 4:=lower_iso isoMv_14_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
def isoMv_22_40:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]
theorem lowS_22_40:Lower true dom_22 roots_22 goal_22_40 4:=lower_iso isoMv_22_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
def dzo_22_8:=0x55005500
def gzo_22_40_8:=0x54004000
theorem lowSh_22_40_8:Lower true dzo_22_8 roots_22 gzo_22_40_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
namespace S_30_32
def pairsG:List (Nat × Nat):=[(2,6),(4,6),(10,14),(10,26),(12,14),(12,28),(18,22),(18,26),(20,22),(20,28),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_30.map (· &&& dom_30)
def goalM:Nat:=goal_30_32 &&& dom_30
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_30 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_22_8 4 s (0,roots_22) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_30 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_22_40_8 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_30==dom_30) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_30 goalM v ys):RunD true dom_30 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_30 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_30 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_30 roots_30 goal_30_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_30_32
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 5:=S_30_32.noCircuit
def isoMv_46_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_46_16:Lower true dom_46 roots_46 goal_46_16 5:=lower_iso isoMv_46_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_32
def isoMv_39_24:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_39_24:Lower true dom_39 roots_39 goal_39_24 5:=lower_iso isoMv_39_24 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_1
theorem lowS_15_16:Lower true dom_15 roots_15 goal_15_16 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00,1,9)] (by decide +kernel) (by decide +kernel) lowS_7_16
def isoMv_39_16:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_39_16:Lower true dom_39 roots_39 goal_39_16 5:=lower_iso isoMv_39_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def isoMv_15_48:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_15_48:Lower true dom_15 roots_15 goal_15_48 5:=lower_iso isoMv_15_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_1
def dzo_38_8:=0x550000005500
def gzo_38_24_8:=0x540000004000
theorem lowSh_38_24_8:Lower true dzo_38_8 roots_38 gzo_38_24_8 4:=lower_iso (d1:=dom_38) (roots1:=roots_38) (T1:=goal_38_24) [(dom_38,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_38_24
def dzo_14_32:=0x555500000000
def gzo_14_48_32:=0x544000000000
theorem lowSh_14_48_32:Lower true dzo_14_32 roots_14 gzo_14_48_32 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_39_8:=0xff000000ff00
def gzo_39_24_8:=0xfe000000ea00
theorem lowSh_39_24_8:Lower true dzo_39_8 roots_39 gzo_39_24_8 5:=lower_iso (d1:=dom_39) (roots1:=roots_39) (T1:=goal_39_24) [(dom_39,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_24
def dzo_15_32:=0xffff00000000
def gzo_15_48_32:=0xfeea00000000
theorem lowSh_15_48_32:Lower true dzo_15_32 roots_15 gzo_15_48_32 5:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
namespace S_47_16
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(1,33),(2,3),(2,6),(4,5),(4,6),(8,9),(10,11),(10,14),(10,42),(12,13),(12,14),(12,44),(32,33),(34,35),(34,38),(34,42),(36,37),(36,38),(36,44),(40,41),(40,42),(40,44)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_47.map (· &&& dom_47)
def goalM:Nat:=goal_47_16 &&& dom_47
def NN:Nat → Nat
|2=>5
|3=>47
|4=>103
|5=>207
|6=>89
|7=>13
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xf5abfec5cd731510773d6b09739827873da2d23a
|3,0=>0xeda7b332c9d27f05c9487f28c271d278a125c22b9f817e9a987a365192a987f5917f375684db65bb83952da7822278027fb09d11791be65078e56bb871d543d96fbb8a706c5bf9966c0a301c6b5a44166b19d7ac663edeab637c20bc5fa0b6325e05a0ee5a5cf5124ad9eb6c4a33add348f3f47b47bea7c743b12fc33dde5287379c8d1d33707a0b234095e01fd609471a8e0d8f166af713157dcdad13930e9410b948fe1095b0b70fd1810e0498a9800483e2410339d1660030eb98
|4,0=>0xee2a8df2e610ba13e36e0171d4604cabce067b46cd684edbc10a9bb7bcd39277bafd2db7b5510dd3ae71326da8b5a6ad9e8ae8209d6eff689aaa13bc99e60d6598c41ccb949210db94657f3f943e46709399c7728b999a798b20ed758425ee7a812b97fd78f0ed817740999c7521af967516c227664608586395d1bb638b31055ecb630d5e00fb3a5465a2de534d1d74524c756d51f3efd4502a28904df787984cb866b34b28a5894b11249e4977e49544b8181143ca0ada43580ad342cb31e93fa6b07f3f6a5a7c3dbd19163b7047953a7d32713a700c3c39db5f0e39a7057538ca2767356578fc3134e0a5307b542c2faa07b62e1b89972de328712dddc4892bfab0b22a37de50291306ef28d1e1da2770021c269a1eba264e425a2368af7420e48a7c1b9d63541929c8ae1918a778187e78fd17d23627179825d6165fe7731590eab414979c61127e399d1064edfb0fcf5d530fba027c0e7533780e73741b0c933b900bd679060bacef850ba86d1a08c618fa06e1a02605fdb23b04cc41f20458dfd4040842db03e609c1033f6f3b0308aefd01b9c65c0019ff09
|5,0=>0x503827224f0ad1d24ea8f22f4e6dc2bd4df515b94d8da9e44d03dbba4a56c18848a92a2948820d0146fa16be46f239ea45624aa9442e01a243ea1acc41792011409f74813e7363463e195d333dfab6423d1c43673cee94b33c58e20e3a27d08539de9b2739d79fc638821eb736ffb74736ad1ea2351f34c33425f1b1333e29c132d03df231baf84d319d7b9d318aaa0a3159221831533559304d165e3038b8282fd71c622f20c09c2e87bde52d6979bd2d17e9942c3f871f2c2009352b67708029cdc00329bf5843293ad03228db2de5287d688227f6552627a6fcca2615e2b3253cb13f2528847225157a382400750123c080dd23a2ab392385a21d230353b720d5237e1fdcbceb1fcf91521fa0c2511f8c9b4b1f0b83501e89a6861e47d0b51e18b7291d6c12e61d3a54a91cc3e76e1a79aa951a4225c61a0211c119ec9e2e18f700241806941717ee37b117ad57ea1716c1c617156baf166de8e6165fe773155ab9b11411d72413aac47a134da0f111f07087113c605a10e825fd10dac407105e97320ff8c0db0fde96530fa662da0f51e8920eef65730dff36cb0c921c310bef86810bacef850acbde0c09da99010939ff6909130cb008fca0ad08c4963e08a766c708a7568107a343bc0761777106e3152906d9bf2006215c0f05c51afb0524f0c1052136230352024a0328ac96023cffdf0105c18700f9f828004bb3fa
|5,1=>0xed3f27b8e3a8179ae0cc0659de5a7b44d5ed365cd37052cecdc2df21c3623d1dc18a3097bebc1b5dbdeb0f97bb1c35dbb66a6f35b61630a8b5c0eef4b5773b81b046bd60af81bcefadfa6a99add532fba7fccd0ea7a45ef4a65f6e00a31d45c4a289c070a25ca54f9fde1ce09c888f039c696e8397b6b99a9750f7ba932833238f76d8cf8ccbeb98891920eb87fd632e87e322d986011b7e85dd8c007edfe7cc78f2336d78276fb4773930c17521af9674c3347673f3dc5373d24f2172b7f62f7202033b71ce4fad714717506fbc4cf86e1c9c6d6da10a776d9e18a06d828dc86b5ba5a86af07299682e913e680860b565ecbce960e1a5e85fc2d9c35f361adc5ebd6dd85d3fa12b5cc93f5b5c6223225c5a6db85b703f935894502b57c26edd5684384354d0de545465a331523f566b51c0721750c22dbd503cd805
|6,0=>0xf7ccf55ef72122fde8d5bbe9e412e5d9e14790c3de30f886d8c17124d8a8b0b6d5d26107bd52b618b7feb98eb3fff31fae73dcb9adfb2fb59839dcb0935188d792f789348f21860d8eb098a684fd11568457dd7480db3d7a7edfe7cc7946e4da78fd1a20752a9aed74126c667234d19e6c84a0df67cd6ed160b4f6295f8491825d4429555b2d6b775a6d65e85a602224551e5568531ec89f523f566b51c8754f4f0ad1d24ded6c714caa10e1494c888f48a92a29476ecf8445d2da7a45ba2a59429235b0404780423d1f024d3b7de6aa3a07fc2a38c18f44384fac7836a67765358bb67232dabc31329dac24312b9b142deb890a2d532f8b29e43aaa28cce7d726ac17ee2616aa1b2512194c1f549bcc1eb3ccb41a6fe39d19898e1c183703e9170c9fe7166de8e6160c1b5b155ab9b1154abe5c146cc86a137fdc2e12ef85350ff8c0db0edf6e590c4f02e7098ee8d90612cec70514ee4f0352024a02a51099029bd3ac
|7,0=>0xe9475e4dcb56f506a2db35a496ac91618151f4be67219c703d6e2c573b576e792ac37c4c2ac1145c27ff330114f99a1c05616d1d
|8,0=>0x3b576e79
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x3333000030300f0c00000f0c55000000550000aa000000aa3030000030300c0c00000c0c00ff0000000000000000ff00fefe0000fcfcffc00000ff0c0f0f0000f0f055ff00000000fcfc0000fffc00ff000000aa03030000000000000000fcfccccc0000cccc5a5a00005a5affaa0000ffaaeac00000eac0ffff0000aa0000fe000000fefcfc0000fcfcc3c300003c3cffff00000000eaea0000eaea03fc000003fcaaaa0000aaaa00ff0000ff00ff000000ff0055550000aaaa3c3c00003c3c
|0,1=>0xf3fc0000f3fc30c0000030c0fafa0000fafaecec0000ecec151500002a2a1e1e00003c3c54540000fcfcfffc0000fffc3c3f00003c3cffc30000c0c0ff0000000300143c0000143cfcfc000000fcffaa0000ff00fc000000fc003f3c00003f3caa000000aa0000000000fefefafa0000aaaaeeee0000e0e03e3c00003e3cff030000ff0c33330000ccccc0c00000c0c055aa000055aaff000000fffcf0f00000f0f0c0ff0000ffc0c0ea0000c0eac0300000c030030c0000030cff0000000000
|0,2=>0xbbbb0000eeeeffff0000ff00fefe0000fefea8a80000a8a8565600005656fcff0000fcfcffff0000aaaaaaaa00000000050500005050f0c00000f0c033cc000033ccff0c0000ff0cf0ff0000f0f0c0c000000c0cccc80000ccc8330000003300333300003232c8c80000c0c0f0ee0000f0ee545400005454323200003232888800008888cccc0000ffccffff0000fcfceeee0000eeeeffab0000ff00555500000000fe000000fe00fefe000000000e0e00000e0ec3c00000c3c000fc000000fc
|0,3=>0xfcfc0000aaaafeff00000000cfce0000cfce444400004444fcfc0000000054ff000000003232000030300f0e00000e0e3f3f00002a2a55000000ff00fafa00000000cccc0000c8c83333000000000c0f00000c0cff030000ff00f0f000000000033000000330ffff0000cccc1030000010300e0c00000e0cffcc0000ffcceeaa0000eeaaff0300000000cfcf0000fcfcfefc0000fefcffff0000f0f000000000aaaacfcc0000cfcc3330000033300ff000000ff0bbb80000bbb8ccc80000c8c8
|0,4=>0xf1f00000f1f0fefe0000aaaafcff00000000bb000000bb00f0f00000fff0ffaa0000aaaa0a0a00000a0ae4e40000e4e4555500005454222200002222f2f20000f2f2cc000000ccccfbfa0000fbfa332200002222f0fa0000f0faf0f00000fafafcfe0000fcfef0000000f000ccc00000ccc0ee000000ee0000000000ffaafff00000fff00f0f00000c0cffcc00000f0c00fc0000fcfc00ff0000fcfc05050000fafa6666000066660f0f00000000525200005252faf00000faf0c0c00000ffc0
|0,5=>0xc8c80000fafaeeff0000eeeebbbb0000aaaa5544000044440f0a00000f0a735000007350eecc0000eecccfcf0000cccccc000000cc00cccc0000f0f0fff00000ccc00101000000000b0b00000a0a0f0e00000f0ea0a00000a0a0ffff0000eeee555000005550fff00000fffcf0f00000aaaa0f0c00000c0ccdcd00000000ff000000ffcccccc0000c0c0ffcc0000ccccbbb00000bbb0332200003322fffa0000fffafa000000fa00ffc00000ffc0ffff000000fc030000000300ffff00000300
|0,6=>0xee0000eeeefefe0000ccccffee0000eeeeffaa0000f0a0444400005544020200000202540000005400fff00000f0f0505000005050ffff0000fefef3f00000f3f0cccc0000eeee515100005050fcfc00005454fffc0000fcfcffa80000ffa8fca80000fca8ab000000ab00c8c00000c8c000f0000000f0303000003330303000003232abab0000aaaaba300000ba3032000000320030300000ff3000000000fff0c0ff0000c0c0afaf0000aaaaeeee0000cccc0f0000000f00570000005700
|0,7=>0x11000000110000000000ffcc050000000500554400005544f0f00000c0c050f0000050f0bbaa0000bbaacece0000ceceffaa00000000f3000000f300030200000302
|_,_=>0
def stPool:Nat → Nat
|0=>0x6073204000731043025060f03070d2f000204002e022d2c0f0702042b072804052a2504290709282707260400250f24040709231d0722042120041f1e071d001c041b1a030906191807021706160f041502090614070213060704001202061110070f0e0a070d090c0b0209060709060a090603020804070605040003020100
|1=>0x4d0f040702254c4b0225474a2e07022506494807023d470746250f0402250f280107020906454344250f0402430f044207250f271a07350400072609060928040307410440073f043e07271b1a040019180709061202041400023d3c2e02250f3b0702043a070206390738310607020437360209040735090607020434070233
|2=>0x3023d2504296635250f0402451b1a650702640442070f0463620702256104070225600402255f042909250f04030702250f5b48070204000732041b1a0744250f0407025a280459020928580702040019020f0415570725560455070d2f1b1a07023d3c0f0754530f04020f5204150725510450070225044f0702174e040725
|3=>0x70204791a07023d3c07020f0478041b1a191802250f587707350928040709280476070233280402752574040204141b1a0702041f1e07023d3c730702041b72250f28040371250f04103869250f0402702c0f04070f04626f6e20250463072504553e0702046d6c076b3d256a69250f041c02680f04150702672804250f041b
|4=>0x209060709250f2707020906190702258483070209043007023d0f82070281060f25060f19180225060f1407020445000709281d1c250f80041902250f042e070d250c0f0709280412027f250f04027e250f0407027d041a073225060f020f047c15070228043907027b0400070f041e4044250f042e02250f047a0738312804
|5=>0x8a8e0f8d04070225060f190209250f042e07025d250f040735250f04076b258c0402250f28048b078a020f0489078802250f0409280419185e250f048702280411100702097b0602250f0486250f040a2e073209280407041b1a125971250f04020928042e07250f231d02250f04850702044b42072609280407250f04054807
|6=>0x4070225640f04029d250f040702090f0489660225490f040738250f041d078a250f9c0402250f04891807029b0f041a070225044f07022547044b079a0225470f07022547980f0702250f0497070d09250f2f07250f270702950f041b076b259404070293250f0466022d0f040702250f04920702910f041b07028f250f0407
|7=>0x590225ad0f0407023d0f046366020f04150702250f04ac070225ab0f04070d250f2f1b078aaa250f046e0225a9046602700f047c078aa8250f040702250fa7040702250f04a60744250f040702250f041e07a5a4250f0407a3250f0445a20702250f04078a3d0f0450a00209250f0407029f250f04073209250f0407029e250f
|8=>0x25b704070209470442660225b60f040702530f2804070d250f04a107b502250f040702250f04b40220250f041f0702250f04b3078a31250f0407022574040732250f041b0209250f45650702250f04b207020f041b89070225478c4a07023d0fb17307020928041db002250f048307250f04af5007250f041a1207ae02250f04
|9=>0x1007020f04c1420738022504630732250f280407250f04c002250f0419100702250fbf040771250f04070225be0f0402250f451b65070225470fbd0702250f04bc070204451b1a0702093d0f4c027b250f046507a80209250407020925475c07250f0450bb070d250f282f0702250f04ba070225b9046d07020925b804076b3d
|10=>0xf04141b070225b9046c07025d250f4c0702250f04c607022564041a66023d750f0402250f284565070209810f046602250f04c509250f041918025d250f042e0702250fc404590253250f046602700f041f6e02250fc304070217250f0407023d0f5c0209250f04144802250f04106e6b20250f04070213250f0402250f0411
|11=>0x4704074425470f0407020f0489cc0738250f041902250f2804140702250f04cb07020925044b0702250f04790702250f0442070225c2041b07022564047c076b023d2547020f04156602250f04730702250f04ca0702810f041b250f041b19180702250fc9044807023d0f040702250fc8040702250f044c0702250f04c70225
|12=>0x225060f450702250f04d3070d25640f040702d2250f045e2009250f0459250f04831248070225047c0702254749040702093d470448070209280407d102250f0407020928041c0702092804190702257d0f0407d009250f040702cf250f040702250fce040702810f2804250f280419180726250f040702810fcd04076b2025
|13=>0xdd02250f040702093d47029d09250f04073831250f0407023d25474b07380d250f0407dc02250f04073509250f04070233250f0407025d25044b250f04030702250f04db0702250f4cda0702250f04d907d8023d0f040702250f04400702042f1b1a078a0f04d750d60702250f0402250f042e07023dd50f0407020925d40407
|14=>0xf5c075d44250f0407d0250f04073820250f04070243250f04070225470f4c0709250f04c00702041b1a19e20209250f040225470f042e078ae1250f040709250f04126e8a20250f040702250f04e007021725c2040702250f04df0702de250f0407a3250f04180702097b28040702250f0487074409250f040702250f043907
|15=>0x702250f04cc070225e30f040702250f04a6076b02250f041e0702250f041e076b250f041d0702250fe4046602700f0407023d25470f070225640f04070209250f04400702250f04581a660702250f047c66076b02250f04b00702250f0407025d250f04078a0225470f0407250f0476072609250f0407020925e30407025d25
|16=>0x407023d250f04e80702250f04e707250f1d1c6e070225e60f040702250f04451b070209250f046507022009250f040702250f044ac166070d02250f04e202250f04480702250f040702250f041107020f04e5070209250f044507250f04126607023d0f040702250f041a19078a0d250f04070225470f99078a023d250f046e
|17=>0xa802250f040702250f047cc10702250f0496c1078a20250f0407023d75250f046602250f0418070209250f04a10702250f044207029b250f046602250f0473070209254704078a0209250f0407025d25470f040702250f044c0702250f2804450702250f04da076b02250f04e9078a020f04d7070225470f04836e076b02250f
|18=>0x250f0419078a02250f041a0702810f04250f041918070225470f044207025d09250f040702250f28042f079a02250f040702258c0f045902250f0483070290250f040732250f040702250f04405e070209250f04070d250f2f070225c20f04070209250f045c070209250f042f0702250f04ea07027b250f04666e02250f0407
|19=>0x2250f0445070225470f04070d02250f040702250f04960702250f040702250f04730702250f041c0702250f04190702250f0458660702250f040702097b250f04070d0209250f0407022025470f040702250f045c5e20250f0407023d25470f040702250f280419070209250f044c070209250f04da48070209250f04070209
|20=>0x702250f045e0702250f04070209250f04070220250f0407
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xc30093006300330003
|3,0=>0xc740c340bf40bb40b740b340af40ab40a740a3409f409b40974093408f408b40874083407f407b40774073406f406b40674063405f405b40574053404f404b40474043403f403b40374033402f402b40274023401f401b40174013400f4
|4,0=>0x205520051fb51f741f251ed51e851e351de51d951d451cf51ca51c551c051bb51b651b151ac51a751a2519d51985193518e51895184517f517a51755170516b51665161515c51575152514d51485143513e51395134512f512a51255120511b51165111510c5107510250fd50f850f350ee50e950e450df50da50d550d050cb5
|4,1=>0x2c852c352be52b952b452af52aa52a552a0529b52965291528c52875282527d52785273526e52695264525f525a52555250524b52465241523c52375232522d52285223521e52195214520f520a5
|5,0=>0x43c64366430642a6424641e64186412640c6406640063fa63f463ef53e963e363dd63d763d253cc63c663c063ba63b553af63a963a3639d63976391638b6385637f63796374536e63686362635c63566350634b5345633f63396333632d63294323631e53186313530d6307630162fb62f562ef62e962e452df52d962d362cd6
|5,1=>0x5b845b265ac65a665a0659a6594658e65886582657c65766570656a6564655e65586552654c65466540653a6534652e65286522651d55176511650b650564ff64f964f364ed64e854e264dc64d754d164cb64c564bf64b964b364ad64a764a1649b6495648f64896483647d64776471646b6465645f64596453644d644764425
|5,2=>0x731672b6725671f67196713670d6707670166fb66f656f066ea66e466de66d866d266cc66c666c246bc66b666b066aa66a4669e66986692668d56876681667b6675666f66696663665d66576651664b6645663f66396633662d66276621661b6615660f660a560465fe65f865f265ec65e665e065da65d465ce65c865c265bc6
|5,3=>0x78a6784677e67786773576d67676761675b6755674f67496743673d67376
|6,0=>0x921691a7913790d6907690168fb68f478ed78e768e078da68d378cd68c768c168bb68b478ad78a768a0789a6893788d6886787f78787872686d5866785f78587851784a7843783e58386832682d58267821581b6814780e6808680177fa77f467ee67e777e167db67d567d057ca67c467bd77b677af77a877a2679c679577905
|6,1=>0x9bf79b879b179ab69a6599f79987991798a7983797c79757970596b5964795d79567950694a6944693e69395933692c79275
|7,0=>0xa0d6a076a0169fb69f569ef69e969e459de69d869d269cc69c66
|8,0=>0xa135
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 235 then fld (dictB (i / 512) (i / 32 % 16)) 48 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 8 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x200f41c08073d43c11250f01e850209c943d250f4943d02094943d250f89411200441c080f0451e672504808100204496592518c1c0a0f044083d900f43c71072501c0a250f4943d073d09411070d80811020f4083e020f4943d250f4943c02470089702094343f02044083d250f0943d0f158083d020f57883070241c085d5cc241109040083d0f15c1c0a250f4943c
|1=>0x2040943d02040951e044c4241325734943c250f40810076b80895020f41c0a020f497090f0442410250f41cbf020401c26020941c95020f41c089b0f41c0a250f4951e02094943d250f0943d0225c943d047343c110904c943d200f41c0809040943c0209c943d07250951e0f044083d250f0943d250f41c3d0209008970204d9811020f4083d020f8083d6e250083d
|2=>0x250443c11250f41e870209c941125478943d020f4943d250f4951e254757883070241c080904c24120f044803d250f40810250f40897250f43c7102048943c0204c1c0807024943d0f1941c0a250f494110f044081225a64097109040342402044943d024cc241302040943c250f6043c250440974254743c11020f4943d250f26c3f09044970a250fc3c1125044083d
|3=>0xf0449411020f4083e020f496590f048343f02045983f020f5983f020f41c13020f411cd020fc083d250443c1125734083f02098943d250f80810020f4083d66044083d09044943d0f044081009048943d090442410250f4097109040943d250f57413254740973090401c3402044943d021ac083d0d09c0811810f408100f0441c0a250f409740904424bf02042a011
|4=>0x2504c9412020fc083d07020091c0f0441c0a020f40827250f4951e0f0443c65070281c3f020f43c11250f4943d020f4951d0f0442413250f4943c0204c2412250f49413020f408970f04408950f0459813020f4081302049983c020f4943e0204c0812250f41c08250f49410020fc083d070d00811250f4943d02040943d020449411020f4943e070281c11020f49412
|5=>0x70241c080204c3c11020443c12020fc0812070280810020f4943d02044943d070203c1109040943d070241c08250443c11250f01c0a0904c943d09048943d250f4943d020f40810254783c1109044943d02040801107020091c0f044083f020443c7102048081002098943d07024943d07044081009040943d02040943d0247c3c1102090943d070f4083d200f41c08
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0xf107080000000d100000000000000000000000000060800000000000000000000b1041814c0000000000000000000020800000000000000c4000000000000000000001080440000010000000000000
|4,1=>0x302000000000000000000005c40001610a88000000000000000000014109880000000000000000000000000000000000000004480001010000000000000
|5,0=>0x12048e24610000000000000228910400000000010888224011f100000000000000f087620000000e0c0003711b080000003510000d0400000019880006422f316900005640001508a084e2261000000048423111080004222010f10708362192
|5,1=>0x40080000007f10000000fc27d10001f040000003d10000f220003c09d88e660000001c840007110001c04da66b2349198cc846313109808be20002f09744b8200000016c40000002c18000ac4551000150400000029114449e44e126893040004b10000000924000
|5,2=>0x6513208000c7163080018a2c3260930057a6bb20002e49702b715b0ad45664b030002b88000ac2558aa84000a910002a054a6a320000000000a0300000013c49b300000013420004c8a5c9286922488a4051e28e1468a28d122881438a1850a284100020c4000812
|5,3=>0x1b84da26c8b58daa20006993448000ce30003308000000
|6,0=>0xa60d28a905462a21508a8053f19e94eca7253729a94cca6252f29694aca52527292948c80012128f947863a31b28c945ca2a513288943ca1c30c2858c286123081838c14a0650127f93f49f64f927b93d49e64f127793b85d84ea27413989ca2e417113809be2de1
|6,1=>0x1741b915c0adc56c2b515a0acc5642b18d886c23601000578ab855b1ac955caaa5532a90d40a9c54d1
|7,0=>0x17f10005f86fa37c1bd8de84001791bc0ddc6ec3751
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 18 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 255),wireSAt ((code >>> 10) &&& 255))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x1003d0e8390c4300b828090210801d0681805c13048110400e0300b02809020070180400c0200400
|1=>0x344ca318c430cc2304c02dcb52ccb22b8a425c85210812007e1d86a1a06615c51128461144410c41
|2=>0x97a4690e1a846007edf77cde775dbd6899d65591635846016255d535094044108405003fcfb3d0d7
|3=>0x3f1f5f93bdef3b7ed8b5ad3a6e80
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x100000000000080040e0000000000070200000000000000000000034007000000000000000000000000000000000050400002000000000000000e000000000007020400000000000e0000000080000000000021000c0000000
|5,0=>0x2600001000020e0010000020008032c1300000415a0008d01031638208815005a0521f000400034006810064000061074490080043e006810000001081c08200000822f7000000980871a04000001420000b80097400001001000004000cf2c00085028cf93000129f1c005820c0700d
|5,1=>0xb01086cf800204021003401f031800202026811d34f010058229047c091000404e3e040380054908000803b0400c1b00000803e0500e1b382335e3ad1f66080950054022
|6,0=>0x2413cf40372cd9605247349c6cb01a8dcec3989eea8ae6db3181868b0658c65f72533683cfc7141479cc120ede676b6c99ca0c5f5878f5a09bcb252b3d0479e86ff3d6b170f57726c462c8511d3
|7,0=>0x691d4ac9e867b5558556be5
|8,0=>0xe
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_45,6,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 1 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 2 then [(dzo_38_8,4,runOps true dzo_38_8 (0,roots_38) ops)] else [])++(if pm.testBit 3 then [(dzo_14_32,4,runOps true dzo_14_32 (0,roots_14) ops)] else [])++(if pm.testBit 4 then [(dom_43,6,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 5 then [(dom_46,5,runOps true dom_46 (0,roots_46) ops)] else [])++(if pm.testBit 6 then [(dzo_39_8,5,runOps true dzo_39_8 (0,roots_39) ops)] else [])++(if pm.testBit 7 then [(dom_39,5,runOps true dom_39 (0,roots_39) ops)] else [])++(if pm.testBit 8 then [(dom_15,5,runOps true dom_15 (0,roots_15) ops)] else [])++(if pm.testBit 9 then [(dzo_15_32,5,runOps true dzo_15_32 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_47 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_45_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_7_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_38_24_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_46_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_39_24_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_39_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_48_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_45 6 s (0,roots_45) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_47 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_45_16 h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_47==dom_47) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 goalM v ys):RunD true dom_47 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 5 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 5 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 47 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 47 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 103 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 39 64=true)
private theorem z4:∀ i,0 ≤ i → i < 103 → Z 4 i=true:=(range_split z4_0 z4_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 207 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 15 192=true)
private theorem z5:∀ i,0 ≤ i → i < 207 → Z 5 i=true:=(range_split (range_split z5_0 z5_64) (range_split z5_128 z5_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 89 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 25 64=true)
private theorem z6:∀ i,0 ≤ i → i < 89 → Z 6 i=true:=(range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 13 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 13 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_47 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_47 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47_16 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_47_16
theorem lowS_47_16:Lower true dom_47 roots_47 goal_47_16 9:=S_47_16.noCircuit
def isoMv_55_8:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_55_8:Lower true dom_55 roots_55 goal_55_8 9:=lower_iso isoMv_55_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_47_16
def isoMv_25_36:List (Nat × Nat):=[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]
theorem lowS_25_36:Lower true dom_25 roots_25 goal_25_36 4:=lower_iso isoMv_25_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_8
def isoMv_23_40:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_23_40:Lower true dom_23 roots_23 goal_23_40 5:=lower_iso isoMv_23_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_1
namespace S_15_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(2,3),(2,6),(4,6),(5,7),(5,13),(8,9),(10,11),(10,14),(12,13),(12,14)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_32 &&& dom_15
def NN:Nat → Nat
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xff00f0f0ccccaaaa
|_,_=>0
def stPool:Nat → Nat
|0=>0xe4
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_32 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_32
theorem lowS_15_32:Lower true dom_15 roots_15 goal_15_32 4:=S_15_32.noCircuit
def isoMv_23_32:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 4:=lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_27_36:List (Nat × Nat):=[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]
theorem lowS_27_36:Lower true dom_27 roots_27 goal_27_36 5:=lower_iso isoMv_27_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_30_1
def dzo_25_4:=0x30303030
def gzo_25_36_4:=0x30202000
theorem lowSh_25_36_4:Lower true dzo_25_4 roots_25 gzo_25_36_4 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_36) [(dom_25,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_36
def dzo_23_8:=0xff00ff00
def gzo_23_40_8:=0xfe00ea00
theorem lowSh_23_40_8:Lower true dzo_23_8 roots_23 gzo_23_40_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_14_16:=0x55550000
def gzo_14_48_16:=0x54400000
theorem lowSh_14_48_16:Lower true dzo_14_16 roots_14 gzo_14_48_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_15_16:=0xffff0000
def gzo_15_48_16:=0xfeea0000
theorem lowSh_15_48_16:Lower true dzo_15_16 roots_15 gzo_15_48_16 5:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def dzo_27_4:=0xf0f0f0f0
def gzo_27_36_4:=0xf0e0e0c0
theorem lowSh_27_36_4:Lower true dzo_27_4 roots_27 gzo_27_36_4 5:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_36) [(dom_27,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_36
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(1,17),(2,3),(2,6),(4,6),(5,7),(5,13),(5,21),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(16,17),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>8
|3=>72
|4=>258
|5=>444
|6=>176
|7=>24
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xda81a5e771f7e93a5e483e8534e1b15934b9d0d134479cc6249ed1a10c3281d8
|3,0=>0xff16b35cdd202854c2f0b857c0fa9d1cbdc842f3b7d7569ab5be682cb2158103b0c90f16ac30c868ab0b9b8ba8bb1ca4a5ff4196a4c04785a1860ef79c114aac9751d43b969b95459489ffa29463b6448f0bf3318dfdeae98c5cb541870bf21d82c5427d824c4d1e80c558dd7da755607c9d943478d6485777f544b66c96a30b64fcbe575ac3a84d56bd354f5624d8345479c62b532d11c152b80ecb4ec91cd449adfe8e459b0020420538aa3d0885cf30f8c54430ca02372c3d959129b187dc2785958f272ae91b1dcbb7ec1b8d6a3619300c80162e3dfa13ff2c7d10ab6ed70fb5d7420fad35960ea95a0e0d4f00450c2a92820ae8822e0a08342909f54dd608eb828e073763080646844505e0a6e905d9543b049be59103ed6cb8018142ac
|4,0=>0x57c06edd5797230856020bba5540f7d4545d46ed543bd6f153e2ee9353611e515104eb2750e72f394e89aad04e535ef34aff15cf49d04d3948982b0b47e1937047c09d6a45f783a5422fe9ab41eadb9741b9574940e74f2f40b5201740904556406290b23d8a95c03d68d77b3d2d28f73ccb0c0d3cbd2aed3c79a46e3ade4e243a2f451f39fae142391ea8eb388094663610e05d35e35b0934d1ec38349b1be13408e1d733c165273333839c32add8d532a0683731caf46a3174431d30f8e44b30de3f903021862a2f4c55192e93dc282e4347382dea06352d5983612d14e5262bda19dd2ba850b22afaef602ac2a1d32a4a059a29d6c43828e032b828d3082d2891333227f386d227ee5dc02581031925139434249f3b7b242d74492382e854218d8791216bd39220ab96c41f5c18181f44bc9b1ef9d35d1e46f3821de0f1b11da9d62c1d4595111bcd7c4e1bad15c11a1b5eae19b6c12a1966aa0d194df6ee18541d7517f20b84177d023417273acf16d5d35216a5359216747167161207c614d74d39146c377f141bf90c140f439f1346e61d1268a15e1192a17f1099fa24101e56660fc2207d0f5427170e7f19660e4d6eb50d163cef0d15f9350c94a4800bfd68380bcb30b00b0cb4f209e6ae0b0878704a0804670406f32a20050e3e9c04de11a804526d9802b20fd2014288fb00b53ad500541227001384d70001c287
|4,1=>0xf85c956ef58a259de60addafe5f16a58e5067c20dec3209bde9d9c6eddcc2ed5dd410db8dd202854dd1f0e2cdc3b1a92d6f98d6ed63958ebd5c88ca2cd78f9abcba2f9bdc77bb510c5ed4cd0c0211129bd434600bc19393aba9fb0edb6cc3816b490ab5ab1e2c06eb1728a5bb0f1c2b6ae9f1206add6bb28a9b3ce12a802f718a7915f88a717454ca693720fa65db836a6501dcba4f3d5d7a1d4d993a087b2a89b8846259add6acb9a8d88729a6b15db99fb3f5d9721d83f96e80abe9624f22f95f361f5953fe93594aaf7509436e6e593e19315935759f39302031c92fcf37092530df2905a515b8ffbf2808fe7a63f8fc98ed28fc8c73d8d1575518c7cb51c8b9b18f38b3123778b0520d6884b20b28825310d8769f47e852c432883f2b2b881d5b3ec81c2b1a9812ed8c17fa199987fa0325f7f5a475d7e97fcb97ccd69db7c0e72647a158b8b78935ef37856399a77b07602771e2ecb7661e3d8751e135a74e09f1373cb6c977326c2bc723b0b507223dde471f3e66e70e7299f6fb027f36dccdf3c6d601d9c6c4dbdde6c3a2bf66ae2c4ab68c52b5568580d7f673090b0671d62db66c71628655b8358632c3f6862d35b04619d870961329bc55f91aa465f8ed8d05ecc106a5ea64bdd5e67c0a95cd85c715b6042115b0cb57f5a9074935a41e17c59d042305976eac45947da4a58ab1b425889f44a58658572585dc020
|4,2=>0xfd221722fbee4419
|5,0=>0x2a067f982970441928d2133b28a5dfd928a153a528671de0286232ed2819bff2274dc3c326c7d1c32683fb59265798b426439a1a250574a2243a9cd224247cf3241dcca4237dd73623708165235ed6af22fe11fc225da82521d08c1121b72497219e44eb2194ce9b218c99b62175128f2172df1b2153b96920212b091febdd111f55c75a1e0f4f6c1cf866c41c91095b1c8c1e681c77b5a01c5f57fc1c0850591bfb90751bf7b3ff1afd20401a81842f1a80579d19d28fd619927a8f197366b7195b1978192a467a18f8723518d80a8418d1621617f89e0017f3b30d1754499016b240b915e918d41580999715781aa115608ba314e3a3de14a9f772146588f3144aa95c1400b75b13e8a55013a7d2f712ef47ae1274ca8e125c25ff118a9fde1183276010e82e3c10d02a8710410323103ee1de0f270bbb0f1e1fb10e5952d00e396ab60e290ae80d9ce5310d8ce2620d3224c20d2f638e0cfe3d380cf234830c287cef0c1c56000c19c63b0bc116290a8ea0600a44a30a0a09a33009bd62ea09b7f91f09a0ff5b097f37b80964c27808d3e2ed086b9afb085d3d8b0733b402072cd911070adda6063fd31205ac37af052037bc04eb34fe04ab1e8a04560df5043b7792043aaec404362bd203fd00cd0326e9ce032583c8032553fa02cc066702174f7101f1297d01b535c90145c582013c4e1a006c12df00422c40001490b5
|5,1=>0x5faeb2875f79ba905ee7f2835e342b405ce9d1295ca3eb205c7f93c35c56672d5c0c808d5bed16d25b02e17e5ae5fc2559c180bc5975e6b5592e7675590076d558fa937858c905b0587b685958740369583f477b566ad2115653f0325395a288527ea26f52756bf95270c8055241b2f1518f50cb5132f1365113bca450a97f3e4f86a6bb4e7506584e4313794d4f55e74cbdce324c93baa04c882d3e4c7b51494c1113e34bdc39c04bc691524bafc7064b8c0e8e4b82a8794b49216d4aebb2864a82231849df6f9249aaa81e48fce79948b5048b48a0eb72486d636648532aec47afb283479c4c93468606aa455d719a44ab55354490ff35448e5572446041bd4408801743f9deaf43b0923643a663bc4358f55041d9c2f6417027cb41206af340b2036a40698c443f8d75dd3f1826db3ef8ff1a3ee413ad3e9cd9dd3e36a0f83ddbc8493d867f143d6f8da13d1825783c07a3c63a5d89983a25460b397794c038f920f138d540b0385af2343859c29f383e6c7137ebd74837721f103766fe2f3751773b36df97b8361ad87335674793354cd925353d53f734ff699034772bce343cd55533cd568f333d681f32a2089d321bd09f3208756731faa9a730ef168230d7c4a530a3b1b12fd9e9472fac25802f85b4322f733b942db294bb2d75eceb2d68cab02c56ab272b373e1f2b252c0c2b184ebe2b0390432aa1ebad2a81d628
|5,2=>0xaed6172eadc7f968ace54ce0ac92ff75ac7ca8f2a85b8c2da8557eb1a7ad298ba5c68f7da5bef5d2a43726a4a365ca18a2643d33a0936428a069d9389fac758f9e4087329ce1902a9cb8f2969c55d9d49b503fd59a8f02cb99c05aac99a422cd97cca01c97855c6d977c37b996334bec9546cda5940192f0937f712c935c6c16933f82d992c354b9926855619252a89a92389b2291a0bc9e9199df38911da88a90dd919690b4ba64908515d58fd5e3168f8f1b778e6c60738d96fe898cc7be5f8c274ef68b4d05908b3123778b2aefdc89fc36f6874012178702ad9884c99b308363db4a82dc6170825e80c88072426a800ea6987ff821a17f755f2a7f5a475d7ea82caf7d47ab107d33ce137cbd0f317b63edf379af023979688a8978a51abe78786220781805207793675877152bec76a37afa75b879dc751696de74799bda74399f5374220d1c7383f09972fafbfd72f0ea6372885be171bd1d2c71a1abf370eabe6070d611ff70c15886709423ab7009cd356f60d2f96ee8e0336e9049e96e8f23fb6e5450a36e282ec06df448946d6f1d036d62400b6ca527146b9cdbb06b61a2bc6b55c1d76ae466b06a3db3b669bbe5486969135868b2351968adf97d6890460268548ee66794fe486794dcb5674f5c8b66f50d9066db5e16661195ac65fb51eb65a58a87658f26fb644338c363d4cfb162909f9661cc5aa060eed288
|5,3=>0xfec1026df483970ff20fc307f01e35afeeee01a8ee54b3c8ee52828dee060b9fed1fa6e3ebc152bdeb85ca54e482d4bcdcec266bdc17eff7db65744ddae275f7da31ec26d9331fc3d6fe7748d442db0fd38269e2d3392061d1fb3644d0fe898ed07e1a33ce642646ce494304cb319a4fcaa1811dca9f5bcbca465fa8c923030bc68ff768c522e6d0c3b97e09c2afcbabc29c4738c28e11c1c244fb55c056389cbfd86441bf3858dcbdf5a666bdbb4216bd38a72bbceebcd0bcded82bbb627323b9a010b7b876a08ab793f47db75c53d9b6ee8092b68243f9b605b3f5b57842fcb4c4f461b34616e4b334c367b06936f8
|6,0=>0x8ee8f8598d0173dd8cc90b268ba1c1528a1b71f6889a1c7688526af68765ed6c86981ddb7f482aa17b470aa67b3a363b79238a6e788c183c75d4341275792668745f33c174064f5d72fafbfd723bc33370adb9596fd5370c6f89a1c16c44dd8a69bbe548642830f263dcfeaa62b6f130615f36ea5fa7b13a5c56672d5930042056e5a25c548f038752906b795081c56d4e0ae47e4c7b51494c1113e34a6d138a49aaa81e491df20a48b8dd14472e25f742e20fee420d2bba416bbb053f4a3df73f1826db3cc52b073b4807623abf1546391cb6163759a6f0371cec763653240c3646b8aa343cd55533208f8132ccbb2831c1c23630ef168230d5ae122f84b7ed2f79e7db2f76ce212f61f1a42ee8d5252e160c322e099d422d9fc0262c56ab272b0390432ae9b5832a4cb9132982f0a928ec7d1328c79243267fe363258fc2bd258c480e241cb7b222fed1a022c5a1b522c2513a22c05eb221d63c9020f514d6207d50091f3073e81dc87bea1d7f95801bf155661b5cdea31a9a6f2417f89e0017f3b30d17232ed716032cd515e918d414e19db814d28d9513a9774813195c2511f26765117beaac10de97a0102cef5f0f2122030e8cab400e61fd760d59fc0a0b67b78a0a8ea06009b5858909a0ff5b08f6698f089d02fa08088c3708025a320728aace05ac37af055409fa043b779204362bd201a76d85017e3b290046f4b6
|6,1=>0xf5d9919cf51082ecf50b0f54ed6072e5eb85ca54ea15b027e64622aee4f3c2c9e2f6cc52e2241facde95aa1ada700e29d5d7a2cece52c4face0b1b63c9b0d7a9c6a4dd9cc522e6d0c44a9845c41b66cbc1d11298c16f4d3dbdf5a666b98f2864b7de3f43b799c159b7959930b58372c9b4374d10b4352449b366aacdb113dc2ab003df99abea8af4aad15876a4249164a2ce3168a0e1d5519f9ebb499daa34649d15bda19c8c6f529abc05fe99c05aac989ce8d797069dbb956a4fd98f7d6f1c
|7,0=>0xd5d7a2ced4201d1ebeb7bba7aacb8ff0974979bd894af9796ec079dc6432baff3e49a49334b0cb8f315e8b562f84b7ed2c56ab272c356191258c480e23aea368202fbf561f16380d1e29e5df1495c976129dfe450d59fc0a09e2bbbd090d6eb4
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x33cc33cc88aa88aa11cc11ccccffffcc00ccccccffffaaaafcfcfcfceaeac0c0ffaa0000fafaeaea9999aaaa0000ccccfafafafa11ee11eefaeaeaeacc3333ccaaaaaaaa3333ccccfaeaeafacccccccc00ffff00ff00ff00f0f0f0f09999666655aa55aa3c3c3c3cffaaff88f0f0c0c0eeeeaaaaffff0000faeafaeaee88ee88
|0,1=>0xfac8fac8cccfcfccdd7700007070d0d0ffff2200f0c0f0c033ff33cc555500000000aaaaffffccccaaaa8888cc00cc000033ffcc5500550000aa00aa888822221111444455555544ffeeccccfcf8f0f0ccff330000cc00ccd0f0d0f0ffaaffaaaa00aa00ff33ffcc3300cc00ffffaa88ffccffcceeaaeeaaee00ee00ddff0000
|0,2=>0x1515aaaaeeee8888ffffff00fac8c8c8ffcc0000ccc0c0cc0f0c0c0c3366cccc50705070cc0000cc0033330030c0f0f033330000ffcceecceeaaaaaaff33ff003300ccccffffaa0014143c3cf0f3f3f0ff000000eeeeeeeebbbbeeee22228888bbbbaaaa2222cccc00ff00aa55007700c0c0c0c05555aaaaaaaaaa88ffaaaaaa
|0,3=>0xf0404040bbaabbaaccccaaaafeaafeaa33000000ffffffccff00cc00cccc0000505050500f3f0c0cf0c0c0c000cccc0003ffff00d070d070eeeeccccfeaaaaaaff22ff88303030300c0c0c0cffaaff00fefeaaaacc00ff000033cccc3f003f00f0f0f0c0f0f0c0f0cc330000000033ccf0f05050f0c0c0f0bbeebbeeaa88aa88
|0,4=>0xfe00aa000f0f0c0cfca8fca810505050f0f0eaea55ff0000ccffcccc3f3f0000ff0033000f000f00f0fffff00000ffaa33003300ee00aa00eeee0000fc00fc00eecceecc3332323233cc0000ffcccccc22220000dc50505033223322ccff00000d0c0c0caf0caf0c22002200aaaa000010f0f0f0ff00aa00faaafaaadc00ff00
|0,5=>0x30707070faaaaaaa00ccffcc55770000fff0faf0f000f000cccc00cc00cc44cccc888888ffeeffee3333ff00f2f2e2e200fe00aa00ffcccceaeaeaeaccaaccaa00fcfcfc00ff00000000ff00111100000000eeeeffabff00ffeeeeeefcf0f8f0bbaaaaaa5500ff000f0c0f0cffaa33001100110000330000ff000300ffeeaaaa
|0,6=>0x33333300fc000000af8c8c8cdd00ff00c0c0eaeafef0f0f054ff000050404040f0e0e0e0f3f300008888aaaa88ccccccd0c0c0c0bbccbbcccc0088005544554405040404f3f3f30015150000ae0cae0cffffc0c0ccccffcc332200000044cccc44cc44cc0f0ff0f0ffaa00aa0f0a00000050f0f0afaeaeae3f2a3f0033222222
|0,7=>0xafaaafaaddcccccceeeeaaee55000000f300f300ff0c0000ffff3300fe00fe0022222222ccc8c8c800eeeeee54fc54fcf0ff00000f0e0e0efcf8f8f80f0c0e0c000f0f00afaf8c8c0f0e0c0cfac0fac00f00ff00feccccccff333300f0fac0eaff22ff0054505050fff0f0f0fa00fa0003ff000033ff0000cccc8888af0fae0c
|0,8=>0xf0f0cc00cccc5151000000f050f0fa000000cc88ffaa005500000300ff0033f300f0f3f3a2a20f0f0000ff33000033332222ccffcc00a0a0a0a05f5f0000551100001100550023230000ff00fffcf0f5000022aaaaaaff50ff50fcfc0000afafaaaa33ff22aaeeaa000044444444666666663300ff000fff0000faf0faf0
|0,9=>0xcc00dd00ffaabbaa550044000f0f0a0aafafaeaebb00000030f0f0f044550000ffa0ffa0aaaaffaa13130000fcfc54545050f0f0ff0c0c0cffff00f003330000af00af00eeaaffaa0f000000afaaaaaa77007700ff444444ffbbaaaafffaf0f0c0eac0ea0e0c0e0c0c00ff0000fc00fcbb00bb00ff0cff0c00ff000cdcdc5050
|0,10=>0x1100ff0033002200ff000f00fffafafaf0a00000705070504444554400220022fff0ff0044440000f5f0f0f0bbaaffaab3b3a0a00f0a0a0aaeaeaeaeaeae00004400ff0011000000fcfcfc0000444444fa00ff0054545454ab00ab00cc880000f333f000f0ffa0aafcfc00fc3300770000f000f073507350f8faf8fa00ff00cc
|0,11=>0xcceecceef050f0504444cccc50f050f0cc88cc88ff88ff88cccc4444ffff00ccff00ffccffff0f00888888880cae0cae00fafafabbbb0000ee000000554444440000ffcc55505050faffaaaa50550000fbfbaaaa0500ff003300030054005400f3000000fefcfefceeff0000aaeeeeeefcf0f0f00c0cff0ceeeeffeecc000000
|0,12=>0xa0a0a0acccccc00c0c0f0f0d0d0d0d030003000f2f2f2f2a8a8a8a8a2a2a2a20f0f0f00f0f0fafa7777000070707070f0f0fff0fff00000f8f8f8f8fff0fff000ff00f00000330005000500
|_,_=>0
def stPool:Nat → Nat
|0=>0x48f81e0b048f41e1f0503c780e1d8241e1f010e81e39050e00c37050100635120241e1f048d01e33048c81c3105024602f010245c1f16828580f048ac1e2a010a41e1f010a04e06130241e251208c122201004420c048801e1f010243c1d048701e1b0d02832180b8282c0c050242a140104c18120883016090803c120707034180b050241002038180a04018080200
|1=>0x20301e0b049941e640118c1e1f120e8680f310301e0b01024c26005024185f05010bc0f2e92c220c01028b84a2d8241e39049681e0b0603cb20b050241e580103cae1f049581e550103c3e540481ca6140b8281e06011481251280241e4f270281e06010281e4d260301e0b0112c7e4a050249248050248e460103c0c450483c880e050648642010e86841011007e0c
|2=>0x40824180a0483c640e01025000c07828120c3c108040a3f8301e020c90c1e451b028120f17828120f2993c040910830fc0a04830fa38011f0120c13940120f3d850f479049e01e02079dc3e02050301e763a8301e0b01028220c048701e74048301e73011c81e1f010282c712e9c0120c378241e0e0101cdc6d361ac120c049a81e690483084680519c1e0e011981e1f
|3=>0x785c140901830042804a48184e05064860f1b028129107808740c3503c140906108a602480251e0f01028120f470d81403079dc04090787d1a0246024420f050241e0e45808148a0603c040a099291217050b0180f41025100c07808140c07a1c0482079b8da02049841e1f01200180f3b808140c4303c04093f214547a010241e1f0d028324342008140c07a0c0482
|4=>0x483c3ea30103cee930d828120f07288040a2e0301e5d50824180f012801413060093e090603c04820603d3c090603c1674010e8183218898140907838040a4e90c1e0205144189c01029360c078081416250301232298c4280a07a68dc6d010281e0618828129907a602e97048301e02140282c0c0502418424b254120c0782c140f371b5282d0b8241e933d0280878
|5=>0x1a18096090603d6a02052d0180f01024180f59828080c07ac89c0a04ac4184005025220c0b82418b007974960c079646c0a339e01e5d048301eaf020301eae56828260c562ac04aa048301e02360301ea5050301e9e4a009520a09830040a540301e02280e8180f050241e3007068040a07818040a098314e0205010e20f010301ea6528d8800a049294817048301e02
|6=>0x62824180f29828180f6230c040a063081e09060e0d037050241e0e18808503a0609c04090603d82020504c18c005024184237008140c07afc04231d0881e020504d7c0c010241e935e88c123407af06c05049e01e025dae8180f0102808b90782418560782d04090794d708c048301e0b050241e535c00832090601c040a049296e3620028260c04870180f058096c09
|7=>0x4944184b04870180f050241e0e2400814010609c6c0a049e05c360512c264a050241e53230281247078381409063346e02118244437010241e1f320d81409018d46c2805024060a1d030703701010180f22828120f29b20040a6603cdc020523c1ea56582812ca0780846340795c140907b259002140304ea52e92c080c07808143a07b1c043a1a03cc00a0603c64c6
|8=>0x78e4140907b50a66c048301e98010301ea64f024d40f51050144b0483c1c020534c180f010241e930e828120f299a4040a04ac5320229024680f01025a40f010241e840f808a4096883c042304889a002050301ecf0603d4aae56824180f0586c04090610c0e02050e81e89010c8dc6d18808d80f371b404090601cda02051c41ea527240120c0792d9c090603c2e0a
|9=>0xd08c123442175bc090603c040f3b87d260205024a20c0102818dd0780846091a10412dc0794c28021409cdc6d0502418db1c208180f3b94c800a09830a60205368180f05024180f6c80814110603c040a0603db082048301e532702812220600814d70603c80090621126020504c949941358120c07828120f070bc046c0603d3c0a04b555814011981e93150084609
|10=>0x78d41ce925824180f0b828740c07828120f071ec040a740301ee70483ca61401024ca0f0f808140c07b9804094403c3ee5048301e0b01028020c1900880e40483034020483c3e090603dc6ad0c824180f05868140c42294040a258441882048301ee20102808e107938143a0603cb650048301e0205031c00f4612c120f6f80874210603c040a28830ee82098301e53
|11=>0x7809040c07a94040c07a788a02050301ef2048301e0b2a8d814092f03c040a788301e02050301ef0048301e0b77828080c07aac040a3802418090603cda0b258241edf0d80814ea0983c040a0603d380205011940f01028020c1b97496750603c048c0504c940a25831dc0f0b828180f768083243190c4040a760301e17048301eeb0110026e40600814ea0483c1409
|12=>0x7808141325031580205024180f6a028120c078e1c402143ec120c0780846090787c040a3a8301e0220028124a06008260c07a4d5c024b92c120c0780814fb0603cee027d028120c07809180a0883096090603caaf9010241e1f013e0128f078081416063dc1409078395c0205025ec0f01028260c7a828740c07a68042907a4c54020510c1ef401028220c413cc120c
|13=>0x7808a0090603d260205024940c2380814090641c1e0205024440c19028120c21008140c079dcf6020502418cc07808464b098301e0205024180f830081409828301e0211824180f7e00814098180814090603e040a048301e5380808140c07a955c0205400180f498081409063fc640205024180f3d82812880603d5a3601028120f2980814097f0301e0205025fa0c
|14=>0x5024180f868085019048304e0286028120c078d814090183c040a4c8301e7701024180f531b4040a020301e37010281907079dc0409108301ea31b08c96090603c0428050301e9e0102a16090603ca00a0483ca61401028120c8500a12090603d2602050249499078d8144b0483ca60214024180f8100815080603cee0205025320c07808140c079de04025b08c1234
|15=>0x1c008d8090610c1e0205024180f8986814090603ca60214024183413808f2090603d2602048301e3249808140c079de1a0205010180f1c0081409890301e0205010180f4200814130603cf60a048301f102980814090603e1e0204830646d1890014090603ca60236024180f36808141904a3c1e0a25825320c0780814090603d6a02848301e774980814090603e1c02
|16=>0x200282609060085009650301e0205458120c078d8144b0483e080205025327807808140c079de261a050301e7729824180f0593814090603cdc1705024180f6202812880603ca6f901028120c0780814134c8301e020603c647749808120c19454621a41024180f2980814092503e2602050251e3407828120f1914c28020483086321897496090603c371405024180f
|17=>0x603c620205024180f8e9740490048301e02098301e324980814094783d260241024180f8e008120f4986c0428048304e930c824180f572b4040a0789cdc6d01100141306008151b048301e0205024191a07828120f29a2c280205024180f7a009180a3a8301e0a04831aa3829808120c07a4e320205024180f8c0283209060e06e0205024180f8b8081413250841802
|18=>0x5010180f49808500a0480c180205284120c078081409288301e0a25b58120c07808140907b1d260205024180f2985c14090603cdc0205025320f29808140c8f03cee0205024192307824183407ab95a0205024180f90808140c078c94a0205480180f3b80814090603d920a0603c65158f808120c079a06e020504c180f8986814130603ca60205024951e078092009
|19=>0x49824180f49ab95a0295028120c07808120f498a86e0a0483ca6a20a00a520a048301f280b828120c0780814090649c1e02048301f245680814094783e4c021425c120c0782896090603ca6020504e360c0780904090603d2c020525c180f3b8d814093c03c6a020512c264a060d8500a049e01e02050301e772980814090603e4a0205010180f18974040a020301e02
|20=>0x49281e0211824680f51008143a0603c700246028120c07808143a0603d084b048301e8449868040a020301e0205024192c07808120f4224c54021402832430780846091a03c6e0205025320f8200814ce048301e02050251e0f36808144b0603cb20204830fc324980814090603d5e0a258301e7729808140c0789d3c4b048301e931b80850090609cda02048301f2b
|21=>0x7292c120c078082e090603d2602064bc1e774980814090603d880a048301e535580a640a048301f3105024180f299749619048301e4b048301e535682896130603ca602050301ea51b80846091a03c700205024180f98008120c9783d260211824680f42009180a0603cee0205025720f49828120c07bf0a6027d824180f570081409970301e0a04830fa0f29809180a
|22=>0x4c8301ead01028180f3ba8c040a061a81e770123014130603c040a9a024180f0125c180f3b808140c07a795c0211824680f68029e6090603c700a04a44180f2980814090603d460205024186a07808120c07c095c36051e01e7701028180f1c294120c079b55cad01064120c07914040a061e01f3301024180f340c4040a0483e0913010a0120c5803c0497048301e5d
|23=>0x79381419048301e02118263c0f01028124307a24040a25810180f01028740c07a4c040a0603e665301028080c07bdc14090603d6aad0112dc8090603cf43605024f00f0120812ba0603c044b048301ebd01028120c3f09c040a04a641e6e1192c120c0794c0537048301e93010a0120c3503c1409064d81e5301028120c07cd5f20a048301e7b050241e53560501409
|24=>0xd008120f498a9180a258241e5301028180f3bcf004fb048301e3201028180f528c4ba02050301ea5010293a090603c040a064ec1e0205024193a07808140c07ce4040a0483e266e27028120c1a03c052805024180f01028440c079dc048c050241e5301028120c07ce05a1705024180f010a0120c1924c040a098301ea325824180f6f8081413061a81e0205024440c
|25=>0x61f9464e05024180f498081409064fc1e0204830f00f5300a7c97048301e02050301e770d8084609061a81e5d25824180f3680814090603e7a0205024181e5192c12880603d260204a201e931500814090787d260205024940f0d85c1419048301e02050241e0e01028120c0786c044b09b90180f0d008143a0603c6c0205010180f050248e0f29850040a0c90c1e27
|26=>0x5518120c078081545048301e020503cdc6d1b828180f3b94d5a0205024180fa2008120c3503e861a053cc120c0780814090603e840205504180f498092e090603d5c02051e4180f3b8d814090603d640a048301e5356808120c079b48a02051f0120c078d814093c03d5c0246028120f82008120c07a4e800205024180f7a828120c07ad4a6360512c080c078081409
|27=>0x10b414090603c040a04944180205534120c07808464b048d01e0205024180fa6008120f0fa4c0409650301e3201028180f2c82a10090603d5c02118e8680f0512c120f298501409440301e3801028f2130603c040aa5824180f41024180f298081409065241e170502419480780a444b048301e02048301ea6298081547048301e02050301f423b8a0120c0794d5a02
|28=>0x1a03c0423048d01f5801029bc090603c040a0603d089e2812c120c0794c0557048301e931b008143a0603c040a02128180f0b828120c079b4144b0483ca61b0108cf2090603c040a0603cef5601028960c07a94040aaa824180f01028120caa03c040907879262a01028120ca983c040a048301f5201028120ca803c040a048301f4f01028120c238e0040a048301f4e
|29=>0x61e0703705064120c07a68040a048301f620102813610603c040a065801e7701230140c07964040a0c90c1e3201028120c07d7c0482048301f5e01208120c1a03c055d048301e930157014090603e280a048301f0f0b828135b0603c040a04831a20f01028180fad24c04e505024180f01028080c07ab4040a048301f590112c12210603c2e0a04830860f0108cb609
|30=>0x50301e9e010283243078dc50090603d2694050241e0e0b828120c07b20040a259d4180f0128014090603c040ab30251e0f0102813650603c1409060e0a6371b028120fab008140901831091405024180f29824180f1c24d5c021192c180f5280920090603c4e0a0483ca67b0a0081409065901e0204830646e1880815630603c0482048301e930d008140f371b41409
|31=>0x780814090603ed8020502418477b80814130611c1e0a079dca6141b10014090603c048c05064120f0102ad6090603c040a04831fe2701028120c07ae0040a048301f6a0102812210603c040a1d0301ead0102812992183c040907a4c54ad010281847079dc040a048301f69012a414090603c040a048301f680102ace090603c040a048308e0f01028120c5383c3402
|32=>0x1028124a81809180a0483cda360512c180f3b80814090603ee85d4612c120c0780814090603ee60a258241972078d8144b049281e0205026e20c078d8144b048301e0205024180fb800846091a03ede0205024180fb712c120c0794d26020502418b707808800a2584c180205025620c1b80814130603ed40205024180f6000814160603c96090603c1602055b4120c
|33=>0x1c0081409060d01e8401028120c078c8da0205024940c07de0040a048301e0205025320c0780aee090603c040a048320e0f010a01409061e01e0205064120c078e0040a0c824180f420081409060d01e370102a10090603c040a048301f020102904090603c040a048301e7b1b00814090794c040a048301ed5298081419048301e37bb00814090603c040a098301f73
|34=>0x603c3602055f8180f01028264a0603c040a048301f7d01028120c078e1260205024180f4224c040a04928180f2980814090603e261a05024180f29808500a048301e5301028180fbe008120c078c9260205024180f19454040a048301e931b8081409061e01ead01028120cbd83c040a250301e7701028120c0794cf602bd024180f01028120cbc83c040a04830680f
|35=>0x1028120c2183c6e020525c120c0780814090603cee5301028120c0794c040a04832460f05024180f4a0081409060d01e312e8081409060d01e0205024180f368dc040a048301f6f01028120c8f03c040a6b024180f0108c14090603c040a048301f242e8081419048301e0205026fe0c07808140c3c03cee02050301e9e01028120c0794d5a0241024180f010289609
|36=>0x48301e0246028120c0780814130603ca60205024180f29d0c040a04928180f5180814090603dbe0205610180f01028120c07a4c625d01028120c07a4c040a048301f820512c120c0794c040a048301e93c0808460a048301e530d0081419048301e02050301e7729808140907df4040a098301e0a048301e9a01028120c07a10da0205024180fc000814090603e2253
|37=>0x603e78020512c120c07a4c040a048301e937b8081409110301e1a01028120c079b4040a048301e5357008144b04830680f01028120c07a4d0a027282896090603c040a25864120c0780814090603d460205024186a07974040a048301e6d0125c120c078081409440301e9301028120c3c03d5c3605024f00f01028180f3bc10040a09831ee0205618120c0780b0a0a
|38=>0x1a03c040ac4824180f01028128f0603c040a72024180f01028124aba80814132503014090603f100205400180f01028120f29850040a80024180f0102896090603cda02048306431011b0120c07828120c0794d5a02050301f8701028120c3f03d260228028120c0794c040a3c824180f01100144b048301e0205024180f0d8081409823dc040a04ae8180f298081409
|39=>0x7c54120c07ab95a0291028120c0780814040603c040a048301f8c01028120c07e2c040a04832c00f01028120c078e0a60205024180f4214c040a048301f8a01028128f07809ca0a048301e021402418270102826e40603c042805024180f498081409061e01e3801028120c3c03d080205024180fab0081419048301ead0102b120c0780814f3048301e0214028120c
|40=>0x25824180f2e92c120c078081409065441e0a0483ca61401028120c07d28040a04884180f0102b1e0c07808144b04928180f01028120c079b86e0205024180f49e38040a048308e0f01028120c07a4e860205024180f29a4c042305024680f0102b1a0c07808800a048301e0205024180f36ab4040a048301e5356008140925084180f0108c14090603d260214028120c
|41=>0x3b80814090603eea0205024180f01028120c3c03c040a048301ead01028120c078a8040a04928180f010a014090603c058305024180f01230144b048301e0205024199107808144b048301f0401028120cc803ca6360512c120c078d8042305024180f0102896130603c040a048301efc010289613048301e0205025740c07a4c040a048301f2d01028960c079dc040a
|42=>0x40a048301e020512c120c0780814090603dee0205024180f36974040a048301e0205064120c0780814090603c6e0205024180f1900814090603f240205024180f8200814090603c4e0205024180f4b00814130603c040a048301e530102826090603c042305024180f01028180f
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xa98048c01e600c300498018c00660003
|3,0=>0x8a204410218810840822040101f880f8407a203c101d880e840722038101b880d8406a20341019880c8406220301017880b8405a202c1015880a840522028101388098404a202410118808840422020100f88078403a201c100d8806840322018100b88058402a201410098804840222010100788038401a200c100588028401220081003880184
|3,1=>0x9a204c102588128409220481023881184
|4,0=>0x139289b544d0a263512f2896544a8a24f5125289154480a23b511b288c54458a2275111288754430a2135107288254408a1ff50fd287d543e0a1eb50f32878543b8a1d750e9287354390a1c350df286e54368a1af50d5286954340a19b50cb286454318a18750c1285f542f0a17350b7285a542c8a15f50ad2855542a0a14b50a328505427a81385
|4,1=>0x1d928eb54750a3a351cf28e654728a38f51c528e154700a37b51bb28dc546d8a36751b128d7546b0a35351a728d254688a33f519d28cd54660a32b519328c854638a317518928c354610a303517f28be545e8a2ef517528b9545c0a2db516b28b454598a2c7516128af54570a2b3515728aa54548a29f514d28a554520a28b514328a0544f8a2775
|4,2=>0x278a93b149cea4e2526ea936149a6a4ce5264a9311497ea4ba525aa92c14956a4a65250a9271492ea4925246a92214906a47e523ca91d148dea46a5232a918148b6a4565228a913148908443521f290e54868a42f5215290954840a41b520b290454818a407520128ff547f0a3f351f728fa547c8a3df51ed28f5547a0a3cb51e328f054778a3b75
|4,3=>0x318298ad4c4ca621530e2985d4c24a60d5304298110bfea5fa52faa97c14bd6a5e652f0a97714baea5d252e6a97214b86a5be52dca96d14b5ea5aa52d2a96814b36a59652c8a96314b0ea58252bea95e14ae6a56e52b4a95914abea55a52aaa95414a96a54652a0a94f14a6ea5325296a94a14a46a51e528ca94514a1ea50a5282a940149f6a4f65
|4,4=>0xc74a6355
|5,0=>0x3d8b1ead8f4ac79f63ccb1e4d8f1ac78763c0b1ded8eeac76f63b529d918ebcc75863a931d318e8cc740639d31cd18e5ea7296391b1c758e2ec7116385b1c158dfec6f96379b1bb58dcec6e3436eb1b5d8da2c6cb6362b1afd8d7686b56357b1aa58d46c69d634bb1a458d16c685633fb19e58ce6c66d6333b19894cbaa6576328b192d8c8ac63f6
|5,1=>0x496b249d9242c91b648ab243d9212c903647eb23dd91e2c8eb6472b237d91b4a8d46467323219186a8bd645bb22c59156c8a5644fb22659126c88d6443b220590f6c8756437b21a590c6c85d642bb214d109ac8476420b20ed906ac82f6414b208d903ac8176408b202d900ac7ff63fcb1fcd8fdac7e763f0b1f6d8faac7cf63e4b1f0d8f7ac7b76
|5,2=>0x556b2a9d9542ca9b654ab2a3d9512ca83653eb29dd94e2ca6b6532b297d94b2ca536526b291d9482ca3b651ab28bd9452ca23650eb285d9422ca0b6502b27fd93f2c9f364f6b279d93c2c9db64eab273d9392c9c364deb26dd9362c9ab64d2b267d9332c99364c6b261d9302c97b64bab25bd92d2c96364aeb255d92a2c94b64a2b24fd9272c9336
|5,3=>0x614330899838cc1666083302d580acbff65fcb2fd157dccbe865f132f7197accbd065e532f11977ccbb865d932eb1974ccba065cd32e51971ccb8865c132df196eccb7065b532d9196beab5965a9b2d35968ecb41659db2cd59660ab2a659232c799630cb12658632c199602aafb657ab2bbd95d2cae3656eb2b5d95a2cacb6562b2afd9572cab36
|5,4=>0x6d2b367d9b32cd9366c6b361d9b02cd7b66bab35bd9ad2cd6366aeb355d9aa2cd4b66a2b34fd9a72cd336696b349d9a42cd1b668ab343d9a12cd03667eb33dd99e2cceb6672b337d99b2ccd36666b331d9982ccbb665ab32bd9952cca4564f332619924cc8c66433320198f4cc746637331a198c4cc5c662b331455896cc465620330e99868cc2e6
|5,5=>0x78fb3c659e26cf0e578433c099df8cef6677833ba99dc8cede676c33b499d98cec6676033ae99d68ceae675433a899d38ce96674833a299d08ce7e673c339c99cd8ce666730339699ca8ce4e6724339099c78ce366718338a99c48ce1e670c338499c18ce066700337e99beaadef66f4b378d9bbcadd866e9ab7359b90adc266de336d99b60cdab5
|5,6=>0x840341ed60ead06f6834b418da0bad0576828b412da08ad03f681cb40cda05ad0276810b406da02ad00f68052c0155ffecff967f9b3fb59fd0afe267ee33f599fa0cfca67e233ef99f70cfb267d633e999f40cf9a67ca33e399f10cf8267be33dd99ee0cf6c47b333d819eb4cf5467a733d219e86af3d679bb3cc59e56cf256
|6,0=>0x90a2c835e40ed20078fcbc7cda3d8f1e668f03476d63a8f1cd78e33c701a374d1b468d7346a1a342f19b68cab46416312f18458bebc5e162e4d16c68b2bc579e2aef15168a5b4511e27eb13968993c4ade248f11e688c34445e218b106687fbc3e1e1e2f0eb6872b437da1b4b0d46866bc319e17ef0b87859342b1a14cd0a0684d3424de118f0866
|6,1=>0x9cebce5da720f38b59c2b4df9e6f0d37269b634d9d66c4b35d59ac2cd49a698d34579a02cced666ad3305994bcc89e638d3157987b4c296606f2fd697b3cbbde5d2d2e2796dbcb51e59af2c6795fbcae5a566d2ac7953aca81e532f294594734a256506d27d693bb49c5a4d4f263792eb496164a2f24a7922348f9a46ef2307914bc88da43cb2195
|6,2=>0xa64bd30da978f4b57a57b52a1e944d49c6a4abd239e910d4826a3e351dd68e2d46c5a3335181a8b6b4547a26bd119e880d4397a193d0b1a84eb4216a0d3d04de818f40579ff3cfe567e6d3ee59f434f89a7b8d3d579e73cf21a786b3bd69dc2cec9a756f3a47
|7,0=>0xaabb5545aa96d5456a9fb54e5aa66d52d6a93b5485aa36d5165a8835429aa08d4ff5a7cb53d169dcd4e86a7135371a9acd4d06
|8,0=>0x155d5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 403 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x2e92f01028010290504c1b03c0503b572b50102b0102a0d02805033048302583d0483d05033050321b0290794e0514e010310503f0503c1b03f25832190c50503e0503f190c50503e0503f0602d078380483d0603d0794c0503e1b03c0503c050300503105027010a00503d0503e190c50503e0503f0483d2583d0783b0603d2583d0514e0109f0503c0503e2e92f01028010290109d0503c0794c0514c1b03c
|1=>0x103c050310503301447050330503e0503f2583d048310609d0503c062b5050330483f050330103e050310603d010282583001028062b50103005030050310124d0603d050330503d0103f05030048320503c0483d0103001088050302583f823dd0603f0603e012eb050330103c0103f07a590502711833050310102a0512b063f3010d30503f050300503125831010280503205033050322e92f0102801029
|2=>0x503d062b50102a0483f062b7060c80503f0148a048320103f01033050270503e14033050330603d0102a0503e0103f050330103c05033010280102b0102a0503c0483d2583d01028013900504c010330794c048310503c01028054230483d0603d2583d010280603f0102b2e92f01028010290109d0503c010a00503d050330514f0503305027140330103c04830258320503f048300108c0103f050300483f
|3=>0x503d050330112a010280102801029010280483d0503e05033050330503c25831010280102a0103f050332583105030050310108c050310503c0503107cb5010280503c0503d0503e0609d0503c050330483f0503c01028050330794f010280503e0514e4b83d010a00503d0503e0609d0503c050320102801390010a00503d1b03c010280483f0503e050310503d014930102801028048320103c0503d010a0
|4=>0x25832010280504c0503c010280503d048320503f0103e050310148c25830010280503d05030010a00503d0514c0503341031010a00503d0503f048310109d0503c062b70102a140330503d11824050330603e05031010280504c1b02905024050330102a01028062b525831010280503e0483f1b03f05030050310103f0125b051280483f050300102b0102a050300503e140332583201028010280102905033
|5=>0x50300503105064048310103c11824010310503104832010a00503d0108c060c80794f050330503205544079b5048320103f05033010a00503d01028200320503305032010280102a05030050310124f01033010a00503d0552b0c83f41030010a00503d0483205033010270cab70102a050330794f050318403d0108e0503305031050330503005032258320514f04832010280102901028010a00503d05030
|6=>0x10280603f0603d010847283f0102801028200302583d010280483d0503e050312e92f01028010290125b050330483f2583d0503125831010280103c0502741032050300102a0503320031259b70102804a3d0609d0503c060c80503f0103c050300514d0103c01028010280503d0109f0503c258300102825831010280503f410330503d0503320025010a00503d41030010a00503d0503305128010a00503d
|7=>0x503d050330503d010330489f0503c0103f050330103f0503305030140300503d0603d0483f055d50603c0503e0503f050300503c05030048320503f063dd0603e010a905032062b50102a0503207a5905027010300503d048310503f048310503c0503e05030050640483105030010a00503d0503305033050330503e0483101259050272584e01028255d70603d0603c25831010280483f0503e2583101028
|8=>0x50330603d2e833010290603c0103e0160e010280503301033048310503d0483f050330503c0109f0503c048320503c048ca0503f05033048300503e010ab05032050331183305031054130603f010a20503d0103e0503e048320108e05031062b70102a051b70483205033050660483104831010290503e0483f050300503105033010a00503d010280503e0603d0483d0609f0503c05033050330503314033
|9=>0x125b0103d0503e0609d0503c0504c0603d0603c0603d0483d0489d0503c050330503c010280503e0503f0109d0102a050330603c0794d050330108c050312583d0102825832010280603f0603e05033140270503d01028050330503305030048320503d0102b01028050330102801028050330514f050330483201029050320514f0102b0603f0483f0483d0603e04ab50102a0160c25831010280483d05033
|10=>0x52b70102a0102801029079b5048320c83f04831051280603d04bdf0603e048330503e050330794d0503305033050330103104bdd0603e2583d01028048320102a050330603d05033010270503d0102b0102a051b504832050310c83c04831079b70483225830010280103f0503305033010290609d0503c25825010280503c0503d0504c0483d0103d0103f050300103c05030060c80503f048310102a0503e
|11=>0x10280603e010290503e0503f0603f0503c05033050310603c050300102a050320603d0503d25831010282e83001029010280503301028050310103105031010280483d010c80503f01028050332582701028010280483f
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>0x4000000000000000000000000000000000000000000000000000000000000000000
|3,1=>0
|4,0=>0x2c4000000000000000000000000000000000000000000000024808100000000000000014c0000000000000000000c8000000000000000000000000000002100000000000000000000000000000000000000000000000000000000000000000000000044000000000000000000000000
|4,1=>0x1a1000000006080000000000000000005c40000548000000014100000000000000000000000000000000000000000000000000000000044c00003c800000000000000000000000000000000000000000000000000000000000000000000000e10000000000000003080000000000
|4,2=>0xd040000c880000000000000000000000000000000000000000000000c082f10000000000000000000000b842d100000000ac82a1000029100000000a0425300000000000223000000000000000844201000000007881d10000000070400006c40000000000
|4,3=>0x43200000000000000000000000000000000000100c00000003d30000000000000000000000000000000000000000000f040000ec4000000000000000000e840000000000000000000000000dcc000000000000000000000000000000000003520000000
|4,4=>0
|5,0=>0x7921e040001d4c7411cc400000007120000000000000000006f200006e11b4400000000001ac80001a840001a44000000000019c86611908631184800000005f217845d116c85a115cc00015480001504513000000013c800013844d113044a20000482118800000004510000000
|5,1=>0x2d840002d44b412cc4b212c44af22b840000000ac22a880002a4400029c8a6128cca1228049f127489c1000000026c4000000099225c800000009612544000000092324088e223448c100008b122840002244881000087121848512104000000000020c4812200400000007e21f447b2
|5,2=>0x3d44f413c88f113c040000000ef13b84ec20000ea23a080000000e623944e4138c40000000e120000e010000df13784dc20000db10000da13644d8135c4d5235040003488d113404cf133480003304cb10000ca10000c82000000031c4c613144c323084c112fc8bd22ec8b920000b72
|5,3=>0x4b480004a8c00000000000001291498d24248880004845201478800047091b14684000464518145c400000000000000000000116100000004509131448400043cd0d2430400000000004288000420800041c5061414400040c90123fc8fe10000fd13f040003e880003e08f710000f61
|5,4=>0x56c958355c55610000000000155154c80000000000000000054855110000000540400000014f10000000538400053454c152c400000014a1524548151c544300000000000000000143150494014fc53d2000000000013c100013b14e853824dc400000013614d453324c853114bc8000
|5,5=>0x1961000195165040000001922000000064098e2634400063058b162858910001872610d8310000000000182160080005f897c25ec40000001783000175300017415cc400000000005c0c00000016d300016b200016925a040000001671594800059056315848000580400000015d3
|5,6=>0x7249c637109c317085c117005be26f45bc100000000001ba26e45b816d4db4100000006cc5b036bc40006b840006b45ab26a4800069c9a610001a510001a41000000068c5a210001a02000000000000000000000000000000019d3000000066c999266040000001971
|6,0=>0x8bca2d28aca2a18a0a2628946232884a1f28784000870a1a2860a1628546132844a101838a0d183060a28246081818a04280c60218045ff27f49fc17e89f827dc5f617d45f327c480007bc9ee17b09ea27a09e627909e227845df27749db27649d727549d417489d117405cf17349cb2
|6,1=>0xa14a832a04a8019fc67e19f467b29e867829d880009d0a7319c867119bca6e19b0a6b19a4800099ca65298ca61298065e2970a5b1968658295c6561954654194c6521940a4e293464c192c4000924a472914a441908a4028fc63e18f0a3b18e840008e463818dc63618d0a3228c44000
|6,2=>0xb48ad02b3c6ce1b30aca2b20ac62b146c41b08ac02af8abc2ae88000ae0ab62ad08000ac8ab11abcaae1ab46ac1aa8aa82a98aa51a906a31a84a9f2a74a9c1a68a982a58a942a4c6921a40a8e2a30a8a2a246872
|7,0=>0xb886e110002e010002df1b784000b746dc10000000b6c4000b684000b644000b606d71b586d51b504000
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 14 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x520a0138260480881001f03c0680c81802c0540a0120220400700d01802c050090100180280400600800800
|1=>0x1001fc3d8770ec1d43a0720da1b0348670ca190308600be15c2b0550a8140220430841042003c0680c81802c
|2=>0x24047c8f11a21a410811012003fc768e91ca3786e0cc1822ec5609f13025c4b0921222404588810e21041881
|3=>0x4828c514a2544087d0ea1942a84d08a0f41281d02203404805001ed35a67ccc1812fa5b4b214c27e4f899932
|4=>0x7faebdbcb6f6cec9d88b09602bfd7eaef5d6b6d6cac154ea9547a7a4ee9d537a674c69852ca574ac94523a44
|5=>0x687bdb732d6d9fb31636c4497921036043ff
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>0x4000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000040000000000000000
|4,0=>0x2000001000400000719000100000204000000000400000400000000000000010007000700000000000400000000000000000000000002000000000b0000000200000000000004000000000000010100000004010000000000010000000000020000020000000000000400003f070000000000000000000e00000000000200
|4,1=>0x10000000000000000000001000001000000000000000000000000190010000000000002000000000004000104000000040000000000250400000000070000190007000000000004000400000000000114000000000000460e00000606000200070701000000010000000007020400070e0000020002000400
|4,2=>0
|5,0=>0x7020719032525596d0000272b004804010166700702260200076d00000b051900070e0000050108684600291900300e0032a111320000040e2a07000001250300010b000507570000080000100000016d0b140000000600040004000000080e266e2c1b00260b0779071d004107027f00070f001a1942110015011b00570000
|5,1=>0x47001f04000b0006051701000e1903007b021b07290214000004003f000700000601100015710e000007220401001901250722012101070e6d0001000906046e0117010e14000719040804030c0b006e490113000001002900070229000e0702060211010100011914065800101c000e00010002216d02140e0e01145a2a0714
|5,2=>0x2001057000001005705010100195f011b040105010000001b010708120200000f0208000e1907000743000005003100081000001b4a00026d080042040065030c071900000007010000000000010200005700006d00000e00575740040019191b0e08003f3f3f0e100160a57b0b020001040e01110707006d0e0302290106
|5,3=>0x534010701a16d140b040700076e14046403000001a20400250010200100801e002907020000011b000100000000070207000b05000022380e00076d
|6,0=>0x384e979b8d0ba05688348b2d9360877553365d2c514463aaa82e4589692d967e4b4b4f6e708e9178604b14103a839a74a88c0a0b5e840b07731740167b3d3b8154828f033463034c3e660d07825e6a79857a989d3d6f5765a3358b564d503b3e3b1e543b7150573e3c442f9f2352773c5e6a5d94247b872d7a9266906130869e
|6,1=>0xa75e2370625c9c6c7c01ac66a6a28a108b3e3a1b28019501691784ab99300b157d5b79038b8aa4393072557235890b39
|7,0=>0xa93c755b766655343c558d88188818333c67186b183c3774
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 8 (j % 128);fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_27,6,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 1 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])++(if pm.testBit 2 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 3 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 4 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 5 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 6 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 7 then [(dom_23,4,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 8 then [(dzo_15_16,5,runOps true dzo_15_16 (0,roots_15) ops)] else [])++(if pm.testBit 9 then [(dzo_27_4,5,runOps true dzo_27_4 (0,roots_27) ops)] else [])++(if pm.testBit 10 then [(dom_15,4,runOps true dom_15 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_36_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_27 6 s (0,roots_27) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_27_32 h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 8 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_0:∀ i,0 ≤ i → i < 64 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_64:∀ i,64 ≤ i → i < 72 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 8 64=true)
private theorem z3:∀ i,0 ≤ i → i < 72 → Z 3 i=true:=(range_split z3_0 z3_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 256 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_256:∀ i,256 ≤ i → i < 258 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 2 256=true)
private theorem z4:∀ i,0 ≤ i → i < 258 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 (range_split z4_192 z4_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 320 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 256=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_320:∀ i,320 ≤ i → i < 384 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 320=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_384:∀ i,384 ≤ i → i < 444 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 60 384=true)
private theorem z5:∀ i,0 ≤ i → i < 444 → Z 5 i=true:=(range_split (range_split z5_0 (range_split z5_64 z5_128)) (range_split (range_split z5_192 z5_256) (range_split z5_320 z5_384)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 128 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128:∀ i,128 ≤ i → i < 176 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 48 128=true)
private theorem z6:∀ i,0 ≤ i → i < 176 → Z 6 i=true:=(range_split z6_0 (range_split z6_64 z6_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 24 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 24 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_31 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_31 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31_32 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_31_32
theorem lowS_31_32:Lower true dom_31 roots_31 goal_31_32 9:=S_31_32.noCircuit
def dzo_55_8:=0xff00ff00ff00ff00
def gzo_55_8_8:=0xfe00ea00ea00e800
theorem lowSh_55_8_8:Lower true dzo_55_8 roots_55 gzo_55_8_8 9:=lower_iso (d1:=dom_55) (roots1:=roots_55) (T1:=goal_55_8) [(dom_55,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55_8
def dzo_47_16:=0xffff0000ffff0000
def gzo_47_16_16:=0xfeea0000eae80000
theorem lowSh_47_16_16:Lower true dzo_47_16 roots_47 gzo_47_16_16 9:=lower_iso (d1:=dom_47) (roots1:=roots_47) (T1:=goal_47_16) [(dom_47,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_47_16

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel

theorem signed_to_mono6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (wit : Circuit) (hwm : Monotone2 wit) (hws : wit.size ≤ lb + 1)
    (hwe : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = f x)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hT0 : T.testBit 0 = false)
    (hncT : ¬ IsConst dom_63 T)
    (hS : Lower true dom_63 roots_63 T lb) :
    ∀ s : ℕ, HasCircuitSize 6 f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  rintro s ⟨C, hfan, hsz, hev⟩
  by_cases hhas : ∃ g ∈ C.gates, isNotGate g = true
  · obtain ⟨g, hg, hgn⟩ := hhas
    have hsup0 : ∀ v ∈ roots_63, Avail true mask256 roots_63 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true C.gates roots_63 hfan (fun h => Bool.noConfusion h) 0 roots_63 roots_63 rfl hsup0
    set out := (execN C.gates roots_63).getD C.output 0
    have hout : out &&& dom_63 = T &&& dom_63 := by
      apply Nat.eq_of_testBit_eq; intro r
      rw [Nat.testBit_and, Nat.testBit_and]
      by_cases hlt : r < 64
      · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
        have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
        have h2 := congrArg (fun l => l.getD C.output false) h1
        rw [roots_63_bits ⟨r, hlt⟩] at h2
        have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false = out.testBit r := by
          simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
          cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
        rw [hgd] at h2
        exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
      · have hd : dom_63.testBit r = false := by
          apply Nat.testBit_lt_two_pow
          have h64 : dom_63 < 2 ^ 64 := by decide
          exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
        rw [hd, Bool.and_false, Bool.and_false]
    have hav_out : Avail true mask256 bank out := by
      by_cases hi : C.output < (execN C.gates roots_63).length
      · exact hsup _ (getD_mem hi)
      · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hd63 : dom_63 &&& mask256 = dom_63 := by decide
    have hm256 : mask256 &&& mask256 = mask256 := by decide
    have hm0 : mask256.testBit 0 = true := by decide
    have hR0 : roots_63.all (fun r => !r.testBit 0) = true := by decide
    have hout0 : out.testBit 0 = false := by
      have h0 := congrArg (fun v => v.testBit 0) hout
      have hd0 : dom_63.testBit 0 = true := dom_63_lt ⟨0, by omega⟩
      simp only [Nat.testBit_and, hd0, Bool.and_true, hT0] at h0
      exact h0
    have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
      rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
    have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by
      rcases hc with h0 | h1
      · exact Or.inl (houtm.symm.trans h0)
      · exact Or.inr (houtm.symm.trans h1))
    have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
      rcases hc with h0 | h1
      · exact Or.inl (by rw [h0]; simp)
      · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
    obtain ⟨s0, ws, hs0, _, hws_sub, hrun⟩ := reach_to_run hm256 hm0 hout0 hR0 hnc_256 hr hav_out
    have hws63 : ∀ w ∈ ws, Avail true dom_63 roots_63 w := fun w hw => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws_sub w hw)
      exact Or.inr (Or.inl ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩)
    obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach true dom_63 roots_63 0 roots_63 from rfl) hws63
    have hL := hS q next hq (avail_of_eq houtm hav_q)
    have hlt := countP_not_lt hg hgn
    have hsz' : C.gates.length ≤ s := hsz
    exact ⟨wit, hwm, le_trans hws (by omega), hwe⟩
  · refine ⟨C, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, by simp [isNotGate, h]⟩ hhas


def newGoal : Nat := 0xeee8e8e0eee0e0a0
def rearranged : Nat := 0xfeeaea00eae8ea00
theorem sliced : Lower true dom_63 roots_63 rearranged 10 := by
  exact lower_slice (dSub:=dzo_47_16) (TSub:=gzo_47_16_16) (rootsSub:=roots_47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000,3,19)] (by decide +kernel) (by decide +kernel) lowSh_47_16_16
theorem paid : Lower true dom_63 roots_63 newGoal 10 := lower_iso [(0xa0a0a0a0a0a0a0a,3),(0xcc00cc00cc00cc,6),(0xf0f00000f0f0,12),(0xff000000ff00,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliced
def solution : Circuit := ⟨[⟨.or, [4,3]⟩,⟨.and, [6,1]⟩,⟨.and, [7,0]⟩,⟨.and, [2,1]⟩,⟨.or, [8,9]⟩,⟨.and, [10,5]⟩,⟨.and, [4,3]⟩,⟨.or, [12,2]⟩,⟨.or, [7,0]⟩,⟨.and, [13,14]⟩,⟨.or, [11,15]⟩],16⟩
end PEqualNP.Outside.L_meta_45634_aux

open PEqualNP.Outside.L_meta_45634_aux in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_45634 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4007714976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 4007714976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact signed_to_mono6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4007714976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) newGoal 10 solution (by simp [solution, PEqualNP.MetaComplexity.Monotone2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold IsConst; decide +kernel) paid
