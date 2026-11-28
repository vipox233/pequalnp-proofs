import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30546
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=18446744073709551615
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
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 64):=by
  rw [show mask256 = 2 ^ 64 - 1 from rfl, Nat.testBit_two_pow_sub_one]
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
  (T >>> (w * i))&&&(if w==64 then 18446744073709551615 else if w==20 then 1048575 else if w==18 then 262143 else if w==9 then 511 else if w==7 then 127 else if w==19 then 524287 else if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519)&&&4294967295
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
def xs64 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def dom_41 : Nat := 0x30300000303
def goal_41 : Nat := 0x30200000200
def roots_41 : List Nat := [xs64.getD 0 0, xs64.getD 3 0, xs64.getD 5 0]
def dom_42 : Nat := 0x50500000505
def goal_42 : Nat := 0x50400000400
def roots_42 : List Nat := [xs64.getD 1 0, xs64.getD 3 0, xs64.getD 5 0]
def dom_49 : Nat := 0x3000300030003
def goal_49 : Nat := 0x3000200020000
def roots_49 : List Nat := [xs64.getD 0 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_52 : Nat := 0x11001100110011
def goal_52 : Nat := 0x11001000100000
def roots_52 : List Nat := [xs64.getD 2 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xe0a0e00
def roots_27 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 3 0, xs64.getD 4 0]
def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0x32322200
def roots_29 : List Nat := [xs64.getD 0 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 4 0]
def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xf0e00000e00
def roots_43 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 3 0, xs64.getD 5 0]
def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0x333200002200
def roots_45 : List Nat := [xs64.getD 0 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 5 0]
def dom_46 : Nat := 0x555500005555
def goal_46 : Nat := 0x555400004400
def roots_46 : List Nat := [xs64.getD 1 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 5 0]
def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xf000e000a0000
def roots_51 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0x33003200320000
def roots_53 : List Nat := [xs64.getD 0 0, xs64.getD 2 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0x55005400500000
def roots_54 : List Nat := [xs64.getD 1 0, xs64.getD 2 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0x303030202020200
def roots_57 : List Nat := [xs64.getD 0 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_58 : Nat := 0x505050505050505
def goal_58 : Nat := 0x505050404000400
def roots_58 : List Nat := [xs64.getD 1 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_60 : Nat := 0x1111111111111111
def goal_60 : Nat := 0x1111111010100000
def roots_60 : List Nat := [xs64.getD 2 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfefaee00
def roots_31 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 4 0]
def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfffe0000ee00
def roots_47 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 5 0]
def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xff00fe00fa0000
def roots_55 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 2 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xf0f0f0e0e0a0e00
def roots_59 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0x3333333232322200
def roots_61 : List Nat := [xs64.getD 0 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0x5555555454504400
def roots_62 : List Nat := [xs64.getD 1 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]
def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffffffefefaee00
def roots_63 : List Nat := [xs64.getD 0 0, xs64.getD 1 0, xs64.getD 2 0, xs64.getD 3 0, xs64.getD 4 0, xs64.getD 5 0]

namespace S_41
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (8,9), (8,40), (32,33), (32,40)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_41.map (· &&& dom_41)
def goalM : Nat := goal_41 &&& dom_41
def NN : Nat → Nat
| 2 => 1
| 3 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 2, 0 => 0xbcb
| 3, 0 => 0xbcb
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x3030000000000000300000003000000020200000202
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x1010008080
| _ => 0
def stOffB : Nat → Nat → Nat
| 2, 0 => 0x3
| 3, 0 => 0x33
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_41 goalM s ys := by
  simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_41 goalM v ys := by
  simp [cutRoot] at h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_41 goalM v ys) : RunD true dom_41 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_41 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_41 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  have heq : mkCut = (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) := rfl
  rw [heq]
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_41 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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

namespace S_42
def pairsG : List (Nat × Nat) := [(2,10), (2,34), (8,10), (8,40), (32,34), (32,40)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_42.map (· &&& dom_42)
def goalM : Nat := goal_42 &&& dom_42
def NN : Nat → Nat
| 2 => 1
| 3 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 2, 0 => 0x2343
| 3, 0 => 0x2343
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x5050000000000000500000005000000040400000404
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x1010008080
| _ => 0
def stOffB : Nat → Nat → Nat
| 2, 0 => 0x3
| 3, 0 => 0x33
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_42 goalM s ys := by
  simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_42 goalM v ys := by
  simp [cutRoot] at h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_42 goalM v ys) : RunD true dom_42 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  have heq : mkCut = (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) := rfl
  rw [heq]
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_42 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_42 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_42 roots_42 goal_42 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_42
theorem lowS_42 : Lower true dom_42 roots_42 goal_42 4 := S_42.noCircuit

namespace S_49
def pairsG : List (Nat × Nat) := [(1,17), (1,33), (16,17), (16,48), (32,33), (32,48)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_49.map (· &&& dom_49)
def goalM : Nat := goal_49 &&& dom_49
def NN : Nat → Nat
| 2 => 1
| 3 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 2, 0 => 0xaa458
| 3, 0 => 0xaa458
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x300030000000000030000000300000002000200020002
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x1010008080
| _ => 0
def stOffB : Nat → Nat → Nat
| 2, 0 => 0x3
| 3, 0 => 0x33
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_49 goalM s ys := by
  simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_49 goalM v ys := by
  simp [cutRoot] at h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_49 goalM v ys) : RunD true dom_49 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_49 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_49 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  have heq : mkCut = (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) := rfl
  rw [heq]
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_49 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_49 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_49 roots_49 goal_49 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_49
theorem lowS_49 : Lower true dom_49 roots_49 goal_49 4 := S_49.noCircuit

namespace S_52
def pairsG : List (Nat × Nat) := [(4,20), (4,36), (16,20), (16,48), (32,36), (32,48)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_52.map (· &&& dom_52)
def goalM : Nat := goal_52 &&& dom_52
def NN : Nat → Nat
| 2 => 1
| 3 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 2, 0 => 0x72e65
| 3, 0 => 0x72e65
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x1100110000000000110000001100000010001000100010
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 3 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x1010008080
| _ => 0
def stOffB : Nat → Nat → Nat
| 2, 0 => 0x3
| 3, 0 => 0x33
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_52 goalM s ys := by
  simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_52 goalM v ys := by
  simp [cutRoot] at h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_52 goalM v ys) : RunD true dom_52 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_52 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true :=
  span_ok (by decide +kernel : span (Z 2) 1 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_52 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  have heq : mkCut = (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) := rfl
  rw [heq]
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_52 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_52 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_52 roots_52 goal_52 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_52
theorem lowS_52 : Lower true dom_52 roots_52 goal_52 4 := S_52.noCircuit

namespace S_27
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (2,10), (3,11), (3,19), (8,9), (8,10), (16,17), (18,19), (18,26), (24,25), (24,26)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
| 3 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 3, 0 => 0x77db1
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0xf0f0000000000000f000f00000000000c0c0c0c000000000a0a0a0a
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x608080
| _ => 0
def stOffB : Nat → Nat → Nat
| 3, 0 => 0x4
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_27 goalM s ys := by
  simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_27 goalM v ys := by
  simp [cutRoot] at h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_27 goalM v ys) : RunD true dom_27 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  have heq : mkCut = (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) := rfl
  rw [heq]
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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
theorem lowS_27 : Lower true dom_27 roots_27 goal_27 4 := S_27.noCircuit

namespace S_29
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (4,20), (5,13), (5,21), (8,9), (12,13), (12,28), (16,17), (16,20), (24,25), (24,28)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_29.map (· &&& dom_29)
def goalM : Nat := goal_29 &&& dom_29
def NN : Nat → Nat
| 3 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 3, 0 => 0x80566
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x33330000000000003300330000000000303030300000000022222222
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 4 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x608080
| _ => 0
def stOffB : Nat → Nat → Nat
| 3, 0 => 0x4
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_29 goalM s ys := by
  simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_29 goalM v ys := by
  simp [cutRoot] at h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_29 goalM v ys) : RunD true dom_29 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  have heq : mkCut = (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) := rfl
  rw [heq]
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_29 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_29 roots_29 goal_29 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_29
theorem lowS_29 : Lower true dom_29 roots_29 goal_29 4 := S_29.noCircuit

theorem lowS_43 : Lower true dom_43 roots_43 goal_43 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c, 8, 10)] (by decide +kernel) (by decide +kernel) lowS_41

theorem lowS_45 : Lower true dom_45 roots_45 goal_45 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_41

theorem lowS_46 : Lower true dom_46 roots_46 goal_46 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x505000005050, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_42

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_49

theorem lowS_53 : Lower true dom_53 roots_53 goal_53 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30003000300030, 16, 20)] (by decide +kernel) (by decide +kernel) lowS_49

theorem lowS_54 : Lower true dom_54 roots_54 goal_54 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x44004400440044, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_52

theorem lowS_57 : Lower true dom_57 roots_57 goal_57 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_41

theorem lowS_58 : Lower true dom_58 roots_58 goal_58 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x505000005050000, 32, 48)] (by decide +kernel) (by decide +kernel) lowS_42

theorem lowS_60 : Lower true dom_60 roots_60 goal_60 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x1100110011001100, 32, 40)] (by decide +kernel) (by decide +kernel) lowS_52

theorem lowS_31 : Lower true dom_31 roots_31 goal_31 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0, 16, 20)] (by decide +kernel) (by decide +kernel) lowS_27

theorem lowS_47 : Lower true dom_47 roots_47 goal_47 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_43

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_53

namespace S_59
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (2,10), (2,34), (3,11), (3,19), (3,35), (8,9), (8,10), (8,40), (16,17), (16,48), (18,19), (18,26), (18,50), (24,25), (24,26), (24,56), (32,33), (32,34), (32,40), (32,48)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
| 6 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 6, 0 => 0x260ba
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0xf0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x40608080
| _ => 0
def stOffB : Nat → Nat → Nat
| 6, 0 => 0x5
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
| _ => 0
def opOffB : Nat → Nat → Nat
| _, _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
| 0, _ => []
| n + 1, p =>
  let code := fld (opPool (p / 64)) 16 (p % 64)
  (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 18 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
| 6, 0 => 0xf
| _, _ => 0
def PM (s j : Nat) : Nat := fld (pmB s (j / 64)) 4 (j % 64)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_43, 5, runOps true dom_43 (0, roots_43) ops)] else []) ++ (if pm.testBit 1 then [(dom_51, 5, runOps true dom_51 (0, roots_51) ops)] else []) ++ (if pm.testBit 2 then [(dom_57, 5, runOps true dom_57 (0, roots_57) ops)] else []) ++ (if pm.testBit 3 then [(dom_58, 5, runOps true dom_58 (0, roots_58) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_59 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · exact cpcs (by decide +kernel) lowS_58 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_58 5 s (0, roots_58) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_59 goalM v ys :=
  checkRootSub_sound (by decide +kernel) lowS_58 h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_59 goalM v ys) : RunD true dom_59 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_59 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_59 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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

namespace S_61
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (4,20), (4,36), (5,13), (5,21), (5,37), (8,9), (8,40), (12,13), (12,28), (12,44), (16,17), (16,20), (16,48), (24,25), (24,28), (24,56), (32,33), (32,36), (32,40), (32,48)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
| 6 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 6, 0 => 0x667d8
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x33333333000000003333000033330000330033003300330030303030303030302222222222222222
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 5 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x40608080
| _ => 0
def stOffB : Nat → Nat → Nat
| 6, 0 => 0x5
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
| _ => 0
def opOffB : Nat → Nat → Nat
| _, _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
| 0, _ => []
| n + 1, p =>
  let code := fld (opPool (p / 64)) 16 (p % 64)
  (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 18 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
| 6, 0 => 0xf
| _, _ => 0
def PM (s j : Nat) : Nat := fld (pmB s (j / 64)) 4 (j % 64)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_45, 5, runOps true dom_45 (0, roots_45) ops)] else []) ++ (if pm.testBit 1 then [(dom_53, 5, runOps true dom_53 (0, roots_53) ops)] else []) ++ (if pm.testBit 2 then [(dom_57, 5, runOps true dom_57 (0, roots_57) ops)] else []) ++ (if pm.testBit 3 then [(dom_60, 5, runOps true dom_60 (0, roots_60) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_61 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · exact cpcs (by decide +kernel) lowS_60 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_60 5 s (0, roots_60) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_61 goalM v ys :=
  checkRootSub_sound (by decide +kernel) lowS_60 h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_61 goalM v ys) : RunD true dom_61 goalM v (ori ys) := h
def Z (s : Nat) := barP true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_61 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_61 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_61 roots_61 goal_61 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_61
theorem lowS_61 : Lower true dom_61 roots_61 goal_61 7 := S_61.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2,10), (2,34), (4,20), (4,36), (6,14), (6,22), (6,38), (8,10), (8,40), (12,14), (12,28), (12,44), (16,20), (16,48), (18,22), (18,26), (18,50), (24,26), (24,28), (24,56), (32,34), (32,36), (32,40), (32,48)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
| 3 => 4
| 4 => 16
| 5 => 30
| 6 => 8
| 7 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 3, 0 => 0x8533b3cb0805b9a02408
| 4, 0 => 0xa57d28afaf7f76478a435e5465b7435651a4d9a9446c137fff32ef7220a7142b809fc108da3062ed
| 5, 0 => 0xe739bdb08ada6add7e82c43889b3db8298b80e717edb47bc996e9116759266cc661a6e60ec5548f04d0d3459a943def3d4803cfc43b5f839e7337d7b31431262ed2251521a071769e02e47
| 6, 0 => 0x9170a8d48d7792a74ca82b75e29a472758f01190
| 7, 0 => 0x9170a
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0x555055505555444455554444050505050404040400005555000044440000555500000000550055555500550000440055004400445454545400000000111111111111110011001111110011001111111111101110555544440000000000450045004400440505010105050000005500550055004455555454505050505555555555550000555555000000000055555555505050505550555000000000550055005500550055555555000000004444444444444444005500550054005455555544444444445554555455005500555555555500550055545554444444445555555544444444555555445500550055550000555500005050505050505050
| 1 => 0x5555555554545454550555055500550000005555000055000101010100000000444455554444444400000000545454540055005500440044555055505550555055555555555055500000000055555500111111110000000000005555000050501111111111110000000011110000000005050505000000004545454544444444000000550000000054545454545454540505050505050000005500550000000055555500555555005555555555555500
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 54 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x24501160049f145008b0024501160049d14045801270501342c0091404009323408b30245011600b8a022c01614045802a3ca0b0024501002498a022c492140430012283811600501002488a20045891e3858012281010024681182c48a02004880a1c08006043000a042000608080
| 1 => 0x1e2908b002450116600091405a0b002450116004b3140458012c85011601889140458012c0501002578d140570b12b4501160048a022c009580c501160158d142c009542808b002548a022c009502808b009848a022c0094a34501169048a022c4a30a28080128878a3c2c009402808b
| 2 => 0x501160048a022c0091404580129c50116004a21a2808b00245015c2c009148408b002428a022c00914045a40025a8a022c009143808b002478a022c4a3
| _ => 0
def stOffB : Nat → Nat → Nat
| 3, 0 => 0x3100084001100004
| 4, 0 => 0x16d405650145404c5011d4042500f54038500cd402e500a540245007d401a5005540105
| 5, 0 => 0x43181066040180fa603d180ee603a180e26037180d66034540cb6031580bf602e580b3602b580a760285809b602558090502298084601f98078601c9806c6019980606
| 6, 0 => 0x4f14136604c1812a60491811e6046181126
| 7, 0 => 0x1415
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 7 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
| 0 => 0x1403142f14011601022d142d00251a2514011484022d1e0314051405160514900025169d1403126d1407160114010a01142d12ad14271a071401129d1403002514011689142f022514051485022d14780225166d1407
| _ => 0
def opOffB : Nat → Nat → Nat
| 5, 0 => 0x88802020078801c20068801820000000000058800000000001420048800000040800e2000000000003080000002880000002080062001080000000880000000000002
| 6, 0 => 0x2a100a440281009c40261009440241
| _, _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
| 0, _ => []
| n + 1, p =>
  let code := fld (opPool (p / 64)) 16 (p % 64)
  (code &&& 3, wireSAt ((code >>> 2) &&& 127), wireSAt ((code >>> 9) &&& 127)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 18 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
| 3, 0 => 0x0
| 4, 0 => 0x0
| 5, 0 => 0xc30152f20000800012c00a05000800600898c00c40020
| 6, 0 => 0x3dfb5ed7a97e
| 7, 0 => 0x3d
| _, _ => 0
def PM (s j : Nat) : Nat := fld (pmB s (j / 64)) 6 (j % 64)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_46, 5, runOps true dom_46 (0, roots_46) ops)] else []) ++ (if pm.testBit 1 then [(dom_54, 5, runOps true dom_54 (0, roots_54) ops)] else []) ++ (if pm.testBit 2 then [(dom_58, 5, runOps true dom_58 (0, roots_58) ops)] else []) ++ (if pm.testBit 3 then [(dom_60, 5, runOps true dom_60 (0, roots_60) ops)] else []) ++ (if pm.testBit 4 then [(dom_42, 4, runOps true dom_42 (0, roots_42) ops)] else []) ++ (if pm.testBit 5 then [(dom_52, 4, runOps true dom_52 (0, roots_52) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_62 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · exact cpcs (by decide +kernel) lowS_58 _ g hchk
    · exact cpcs (by decide +kernel) lowS_60 _ g hchk
    · exact cpcs (by decide +kernel) lowS_42 _ g hchk
    · exact cpcs (by decide +kernel) lowS_52 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_60 5 s (0, roots_60) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_62 goalM v ys :=
  checkRootSub_sound (by decide +kernel) lowS_60 h
def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c, 2), (0xff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_62 goalM v ys) : RunD true dom_62 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s : Nat) := barP true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 4 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 30 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 30 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_62 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true
  rw [← barP_eq]; interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_62 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_62 roots_62 goal_62 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_62
theorem lowS_62 : Lower true dom_62 roots_62 goal_62 8 := S_62.noCircuit

namespace S_63
def pairsG : List (Nat × Nat) := [(1,9), (1,17), (1,33), (2,10), (2,34), (3,11), (3,19), (3,35), (4,20), (4,36), (5,13), (5,21), (5,37), (6,14), (6,22), (6,38), (7,15), (7,23), (7,39), (8,9), (8,10), (8,40), (12,13), (12,14), (12,28), (12,44), (16,17), (16,20), (16,48), (18,19), (18,22), (18,26), (18,50), (24,25), (24,26), (24,28), (24,56), (32,33), (32,34), (32,36), (32,40), (32,48)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
| 3 => 8
| 4 => 96
| 5 => 235
| 6 => 325
| 7 => 134
| 8 => 14
| 9 => 1
| _ => 0
def HT : Nat → Nat → Nat
| 3, 0 => 0xc9ba3589664342a422ec33c782a1c028fce0f2b2
| 4, 0 => 0xf9734efeb3c2ed5c051bbecf9bcc0eb860eb6df0b4840b0b20ac2eca9920a3c2fa2ac2a01829d3949afcd9ab1498f45921fc8f52286734815d17fb487a61f745927417f724777091d6b43868bc063b5962f576214b618635c4a65aede58cae58bfe5586053a1f51c46515c04cbe64abbb48479473a144558438be41fc03bc133b9383ada03a4b0393113684835e77354353337a320bd30f282f1782c7be29d9028a7d283bd282dd27f1b25e982332821a3a2147d2121f1c04e1ba3e1a67c195d618bfe17b581331212f6712ea411c181172a10ea00d4680bdd50bd870ae1309ce8095f708527067ab057bf0375301ff9
| 5, 0 => 0x5dd915d2545c1ec5bb585b3f85b0ad5af9f58a17580ce56fdc53ead529fb528b051b36514275129a50cfb50a5a4e6b34d40e4cc194ba494b6a54b5194b41a4b20d4918b485aa4853346e3446845459bc455a944ebe43b804344042b5c429bc42773415f840abf3d4cc3c8dc3c0473a3dc39fe839f42367da3614b35851335753236c30f4d30f28309cd308ee304692fd0f2e6182d8372d3522be5e2a52d2a028291502912428b47285932837d2805426c5926944252ec24ebe24d482244021526200841f56a1f4e21eea01eb931e94e1d86b1d6be1d0c71c7a81bfe51ae071a6f51a42d18b061867a184f91829a17e1f178e1177dd170aa1706a169121622a15e471428911d4111a1b0ff3c0f7f70e4be0e3a40df1c0d3500b7680a71e0a6000a1790965f07e6a07ba3074ac06b94061980566f0502c02ccb027270235201767
| 5, 1 => 0xfb70df6738f6517eff5fee617eb9cfcb40ec97bec929dc60c9c5204c12ddbf49fbf2a1bec89b8c69b7b3eb6859b602ab469fb0f76b0c6aaf1dfac0bda9931a86e5a8523a8481a6422a40bca2ef4a1f2ea1476a10fe9f36f9ebb29e4249db329cf6a9cb409c9b69c3689bfbd9b4859af1c9949e991fe982ae973f5968a994b42943cb93cac9184090fd28f75a8f68e8f5228f2898e5f88d3dc8cac988cf488711880798703185c6a857d5823888208881f4a81c78814be8059b8037f7fa847f92a7f6227f1457ec417c00f78b79784487714075a51750597018e6fbc06e9f76e7106da796bf3e6b16d6a1e36981969661677d066ea566a03661e565e3a640856362661e0860ddc5fb1e5f854
| 6, 0 => 0x3914c38bfa385a63858337d0e37a573730a36df1368ca34e57334b0331003236c31ab9312f330bc5308ee2fbbc2fa1c2f7e72f3522ebac2dd822d3522cefb2cd972bcd82b8d72af712a57e2a3242a2f729ae42935a28bbb28a2d283bd27b8b26cad26a9c257df254a5240892340322887226c42220821b0c218be2171e20e6e202851f8261ebbd1eb931e3bb1df3e1d70d1cabb1c9401c6371c5e71be8a1bda61b6221a2d71947a18ad51867a17f9517ef3170e216a51163e31575e13d84138fa132a912e65128ba12200121f0113b211268110c310fbb10e2c10b72108651079c102d00fb140f7bc0f45a0f2520d0e50cf360cdb90cc990ca0e0c6dd0c3620bb3c0b5400a7ce0a3920a179098bd095bb0887b07e4a07ba306902065b805e540566f055c905575050e404c030438403e9d03d750375303524029750235200e0a
| 6, 1 => 0x8ac448a5b4899de88ad9861c38234f8135180d9480312802867fd4b7ee807df727dd277aa6c7a3027a0097993f795b278c0a78bc0778fb774c475a517587875120748ee725286faa16eee26e4086d9106d5de6d1fe6ca4d6b0466ab666a2e6686fa6860e684bb676aa65186650d66457e6392c634f761cc161ad360ead600555fca55f0895e7965e7265e0b75d9d35d1ae5c1e15a6ac597be596cc5961e58ccc58b64584dc577565647a54d4853a955368c531a6530a252d1652638524be51b67517305167050a7a500094fcb24e52b4ca8f4c1244bc074aaa24a8f04a8db4a5474a4f1499d1491ff485334815547825473ae46811451df448c543f53439da42d3d42a4c427f1420aa41fb841ba341a12419194128a4113140a09408d3402233fddc3fbf23f0973edbe3e8a23cb573c6c63c3103c2ed3ba613acfe39a4f39580
| 6, 2 => 0xfb1bdf45feed1d9ecad9ec231ebb1fe89bce4be1e086cdbca7d9f70d9946d8fcdd7544d49fbd39cbcf782cdd1acdb8bcc079c742ec1d9dc0739be304bd51aba2d9b9fb2b9a3eb7758b64dbb5eceb0d75affd3af000ae705adb6bace12a5765a51b8a4f20a2c18a1d91a1c8ea1a03a0ff7a036f9f4579ec729e43f9e4249d3949cfe99cf6a9c1bc9af929a6c7973da9721295e2893ea391818915e190fd29001b8fdcf8f7058eef68decf8d3dd
| 7, 0 => 0xd8fcdce7fccdd1ac6728c5bebbd20bb18f4b0ab8afb32ae705a978fa8480a7c7e9bdbf9bd2d9b4959ada9973839648494bf69323691d4e8d20e8b5c689e13896e98797684513836c58324d813517dd277c86b7b28275a5175a47748ee738c2726a56e9526e00f6da796c4c16a8c96a5cf69aef6993668fed6890e66da4640235ef4e5ddbd5da4d5d5345a6ac59b0d5748f54d4852b864c4534bc804a6464a449491ff4886348533476b8473ae46bd0456ae449d842ceb41639415f440e55406983f3903e37e3d73f3d1d93acfe3a0cb37b5d34e753463032503312f32f7e72ddcd2af712a07d289812691f2501423b98239f623280220d920a80206861ed0b1e7521b6221978717a1b157661059b0f45a0e4360dd0c0b0c50948108db70873407f7907b4606c2906b6e06879053f00438403e9d037340340902dba01dfa00b97
| 7, 1 => 0xfd481f45feebfa8ebd33e74cedffc7
| 8, 0 => 0xdd199b8f5c748ee708114f22f485a044034346302f7e72c93017f5113a600b85d02c80
| 9, 0 => 0x4ec9
| _, _ => 0
def dictB : Nat → Nat
| 0 => 0xfffffffaaaaaaaaafffffff0f0f0f0f0ffffff00ff00ff00ffffffff000000000505050505055500ffffffcccccccccc00000000ffff0000ffffbbaaaaaaaaaa0000005050505050ffcfffccccccccccffaaffaaaaaaaaaaffff00ffffffff0000ff0000ff00000000ffffff00ffff00ffffffaaaaaaaaaaffffffffff00ff00fffffffafafafafaffffffeeeeeeeeeeffff0000ffff0000ffffffffffff0000fffffffafafaaaaaff00ff00ff00ff00ffccffcccccccccc0000ffff00ffff00ffffaaaaaaaaaaaa00ff00ff00ffff00ffffffff00ffff00aaffffaaaaaaaaaaff0000ff00ffff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa
| 1 => 0xffffffffffff0f000f0f000f0f0f00000000003333003300ff0000ff000000000000000000ffff00ffffffffffffff00ffffff0000000000afafafaaaaaaaaaa000000ffff00ff00cccccccccc00cc00f0f0f0f0f0f00000ffffff00ffffff00fafafafafafaaaaaffff000000000000ffffafaaaaaaaaaaffafffaaaaaaaaaaffff0000ff00000000ff00ffffffff00555555555555550000ffff0000ffff000f0f0f0f0f0f0f000000ffffffff0000eeeeeeeeeeaaeeaa0f0f0f0f0f0f00003333333333003300ffccccccccffcccc00ff00ffff00ff0000000f0f0f0f0f00fffff0f0f0f0f0f000ff00ff00ff0000000000000000ff000505550505055500
| 2 => 0xcccc3333ccff3300ff00ff00ff000000ffffff00f0f0f000fff0fff0fff0fff0ffffffffff33ff00ffff00ffffff0000fffffff0f0f000000000004444444444f0f0f0f0f0f0fff0ccffffcccccccccc000000ccccccccccccccccccccffcccc00ffff0000000000000000ffffffff0011111111111111000505050505050500ffff00000000ff005555005555555500ff0000000000ff00000000ff00ff000000550055555555000000f0ffffff0f00ff000000ff0000000000ffff0000ff000000000000ff0000000000f0f0f0f0f033333333333333003333003333333300fffffffcf0f0f0f0ffffffffff0000003300333333333300ffccffccccffcccc
| 3 => 0x3333000033000000ffffcfcccccccccc33003333330033303333333300000000bbbbbbaaaaaaaaaaff33ff33ff00ff0033333300333333000000ffff0000000000000f0f0f0f0000ffff0f00ffff0000ffff0f00ffff0f00000000ff00000000ff0fff0f0f0f0000ffffff00ffff000000ff00ff0000000000000000ff00ff00f000f000f000ff00000f000f000f0000ff33ff00ff33ff00ffff3333ffff3300333300003333000033ff333333ff33000f0f03030f0f0300cccccccccccccc00ff00ff0000000000fffffffff0f0f0f0fffffff0fffffff000ff000000ff00000000ff000000ff00ffffccccccffccccff0000ffff00000000000000ffffff00
| 4 => 0x33333333333333300f0f0f0000000000f0f0fff0f0f0fff0ff33ff33ff33ff00ffbbffaaaaaaaaaaffffcccccccccccc33033303330033000f0f00000f0f0000ffff0f000000000000cc00ccccccccccfffffff00000000033333303333333000033003333003300ff00ff33ff00ff003300330033003300ff0fff0fff00ff000f0f0f000f0f0f003333333333033300550555055505550033003333330033005555555555555550ff00ffffff00ff00eeaaeeeeeeaaeeaaccffccccccffcccc3330333333303330ff00ff0000ff0000ffffffffccccccccffffccccffffccccf0f03030f0f03000cccccccccc00cccceeeeeeeeeeaaeeee5555555555055500
| 5 => 0xf0f0f0ff00000000ccccffffccccffccffffffff3300330000cc00ff0000000000000000ff33ff00ff00ffffffffff00ccffccffccff0000ff000000ffff0000ffffffeeaaaaaaaa3330333333003300ffff330000000000f0f000f0f0f00000fafaaafafafaaaaacc00ff00cc00ff0000ff0000ffff00000000ff0000ffff00ffffff00ff000000444444444444440000000000ffff0f005555551155555500f0fff0fff0ff0000f0f0f0f0f0f000f0fafafafafafaaafa0f0f0f0f0f0fff00000f000f0f0f0000ff0fff00ff0fff000f0f0f0f0f000f00ffffffff333333000f0f00030f0f0000fff0fff0f0f0f0f0ff0fff0000000000f3f3f3f0f0f0f0f0
| 6 => 0xff000000ff00ff000000ff0000000000f0f0fff0f0f0f0f000000000ffff3300ffffffff00ff00000f0f0f0f000000000000ff0f0000ff00f0f000f0f0f000f0fafaaafafafaaafaffff3333ffff00000f0f03030f0f00000000f0ff000000000000333300003300ffff0000ff00ff003333003333330000f0f0f0f0fffffff0ff00ffff00000000ffffff000000ff00fffff0f0fffff0f0f0fff0fff0f0f0f0003300330033000000ff000000000000f000f0f0f0f0f0f00f000f000f000f00ffffffff0f0f0f00ccffccff00000000ffffccffffff0000ff00ff000000ff00fff0fff0f0f0fff00fff00ff0f0f00003333330000000000ffffffff0000ff00
| 7 => 0xfcfcfcfcfcfcfcfc0000ff330000ff00ff00ff00ffffff00ff0fff0fff0fff00fffffffffffff0f0ffffccffffffcccc0000ffffff00ff00f0f0fffff000ff0000ff00ff00ff00ccffffffffffffcccc0f0f0f0f0f0f0c0cffccffccffccffccffffffccffffffccf0f0f0fff0f0f0f0ffffffff33330000ffffffff0f0f0000cfcfcfcfcfcfcccc00ff00ff00cc00ccffff00ffffff00cc000000ff000000cc003300330000000000ff00ff00330000fffffffffff0fff03333333333303330ffff0000ffffff00ffff0f0fffff000000f000f0f0f0f0f0ffff3300ffff3300cccccc00ffffff00ccccffff00000000ffccffffff00ff00ffffff0fffffff00
| 8 => 0xf0f0f0f0c0c0c0cffff000000ff000000ff00ff00f000f00000ff00ff00ff00ffffffffffffffcc00ff00ff000f00000000333300000000f0f000f0f0f0f0f00000ccff0000000000000033000000000f00ffff0f000f00ffff0f0fffff0f0000000000fffffff0ffffffffff0fff00ffffffffffccffccf0fff0f0f0f0f0f00f000f000f00000000000f0f00000000ff00ff0fff00ff00ffccffffffccffcc0000ffff0000ccccff00ffffff00ffcc000000000f0f0f00aaffaaaaaaaaaaaaff00ffffff0000000000ffff0000ffcc33333333333300000303030303000300f0f0fffff0f0f0f0f0f0f0f0f0f0f000f0f0fffff0f0fff0ff33ff0000000000
| 9 => 0x303030300000000000f000f00000000f3f3f3f3f0f0f0f0fffffffffcfcfcfc00ffffff00000000cc00cccccc00ccccf0fff0ff000000000000f0f0f0f0f0f0
| _ => 0
def wireSAt (i : Nat) : Nat := if i < 296 then fld (dictB (i / 32)) 64 (i % 32) else 0
def stPool : Nat → Nat
| 0 => 0x150700200158b01401000ac540d0080050250e0341429140300e0a0109c1a26010004a0c050040024060403c010008c020011084380d05004400c0f8280401060783a01000701a0a0086c201a0100032100c03404010604414010b8401a1601000200d0a80802140100400130880802120284404010803c1c0d0602c1401048080008038080206028080204018080200
| 1 => 0x100088250610c1401001083c340080014020010454100690004001f8c414020083402001f094200d010007a3c01004003b060441402008401a15008ac742f0480800051c808020008078340d00030460a00800180a010047002008006e19080441a021b0403834198046402008000c0c188280401080346002008bc0401000b8181a0e808001c010045a2c05008022d
| 2 => 0x1004201106808aa0d01150002502808020029870680214920920200800a41c06828a2500e03c1c0d050402202008649e02008004410070441a02080342a02228340401270942011068084e0c11828022d268080200260401a020092c203906808520a01004004a1d04492020085404012411c3c0d008006e10078441a0105008004515040340d00118380d050cc8a0d
| 3 => 0x308080200300702202008b0201f06808021c01004082c0e028045f000e80e5e01004185d2e004005b0d0340400089681402008441a02008dc185905004000c088280458210446802008300e0a2b80438022b000580d0100400251c808020009040220d009181823050004e100d0441a02080681a02000703c01000b0201e08834020c11828004506040220200830221d
| 4 => 0x11a05a1c068280200348701a0a34000561008834140200834040013894200d1782404000e0d06a0100088183205008002706198ca0a00800841c1a00802000680802001284c38020080058530e0441a0a010040a1c01004002c0608c140100088181c3102804000e03414570080018111c828040106174140200800200d0a8080248060e4140200800181e068280200
| 5 => 0x80340401000b8381e3a82802001d0e4920200800220d0500802740e044684901004380d3982802000e1c83a020080038342f00802000e078140100064180705004500d00800507138030460a00800e010088d01a02008701a6f00800dc1c0680802001b8701a6d010008a1c36028040035840383406808521c06828040035030200705008021c218341401000701a0a
| 6 => 0x10004e1006a18040100070340a010003210428d1080200070780200800581c06829060013870300d05008021c0682804810e034140200a00380d0b0280400051340401000a8386c05008007f0e1f8ea0a0100018230500400210e0341402001f4200d01000f8790e0341402009ec380d3d008007908070e402008001401000a8f077080340401000dc3876050040028
| 7 => 0x13870686101004001c06828028d14070140200230321c0682804014583402001f1c4e01c06a281402448301401001dc742f338080200080e4040100064380d05008022d060401a0901000181105008020c0e0781401000701a0a00800560a2f0080200150701a6d010004e0c050040028150e8200d04808000c0e0280488000701a0a010010e1c0f03414002a840720d
| 8 => 0x6828020006040720200800380d050005096082541a020080038720500400280e0443a0d01004380d0500800940e078340d05000381d068080200068080025498701a9201001220c0e8e4040100040720d01000aa1c1a124040116870140200800101c1a1240200158401a6701150001c01004002c300701a90008011e0c0e0681402000701a0a010011c100e1d40400
| 9 => 0xe0d0040100048380d050045a2b0e0280200151dc380d4d9b40401080280401000a80401001d0327006071340a000a01839050d402000e0341468000a0380d0500132980e169140200800201c06828660108078720d00800181c05008008c0e0341401169401a02008004a1908070220d01004920200800e860060703a01000a1140a01004002a0625c140200800cc95
| 10 => 0x9c84341c80802000e03414021b0b438230682800270e078e40a00800380d050d8002b08034ce020080020390680400461d0300e0a01004380d05008009f0602804010027838020080058741d0441a0a01004201c06a7400270e035380200244740d0100400251d0701a0a010a4380f08834140108068720d010007e97050080200060740401001c03c0d050040078
| 11 => 0x80050770e0341400228ac380d5300400a51c9681402008001a0a0100400520e008020011121480d05008007c1c8340401000dc3811050080219060700e0a008a038110682804580e0341400139a4380d0500400a3060401aa200800381a390280400080354202008006402008004421080681a0200800cc1c0682800990e03414a000800380d010004e250e0341402
| 12 => 0x240701a0a010a4900c038280401108401a67010045a100699c0200158701a1505004500a010040078568701a0a01005581c1a2ac040100030380d052a4020c4a828040100070220d05008aa0c038280401380701a0a01000aa1c391b404010007068020080076100d03404000e1741a5c0080038342f00400280e0341401002a01a02008004a470e03414010029c180a
| 13 => 0xf0d0920100070b40a01220001c068296601080345e15010041a020080044600e03404b20009c380200800583b0e0280200142c4383406808521c3f0341402000701a0a010b44e1c06a6c1402008701a0a0009c561c0f0441a0a00830380a00800ee1c1a0080200580703c0d05004001c1a2bc0401000701a0a008007c1c06828042d5704038341a804000d010040025
| 14 => 0x60703a0a01004000d0100400bc5d908680200800c0ba05008020015071080a012e400050e0d00401000701a0a0009c500a01004002a260357002008004a110682804013c0701a0a010051a100699c040022870720200800581c3aa280401000716e0d0500802100d0d01a02000701a0a1b000501c0682804005b0401a0200095263a0e0080200160416a0d01004001c
| 15 => 0x8001810190280401000701ac305004001c06828040100308381106828040108070ea0d01004001c068080200128701a0a0100400c10e034145700800186606828020014031800d0500802000e03414bf01004001c1a1c8140200800181c050080200320701a0a0100400480e03414025f00400100685404010e03414670080050bd0e2101a0a010001839050080200
| 16 => 0x1004001c3283414010023c18100e0d0040100030640a00800501c6683414cc00800387206828040100030380d050086c000e034140200801961c068280401000ac200d0100400250e03414c900800201c0682804290e034040100320c0c70e034140200800741c0682804360003038070500802100e03414024400038c506828040100108383401004001c2d03414b4
| 17 => 0xe03404003e24438d60682802006a8280401000a8f010068bcce020080038750500802006a030380a00800509806070140200800e81c0682804010034c380d69028040100040680d01004007c0e0d01a0a011a0001c1a034f40200800cc1c1a034b801000701a0a0100400d10e03414d001004000d678280401001c4181c068295401000701a0a0100400ad0e0d19c0a
| 18 => 0x4c071c00d05008020006070680a1a804000a6f80802003c064201c3900802000e0345e0a010004e1c2d0340401001c0380d0537402000e034140200801b81c1a0080200160703a39068080200080701aa200800201c06970020052834140200800f0606d8701a0a01004001c06828040100364380d450080200640701a900500400980e0d0bc0200800380d0535c0210
| 19 => 0x6828040013864180a00801b498060701a0a010008a0c0e1941402008001823050040010428d01a02008010a8406828040038870680a5c008020006071c80a01004003a0e0341402001143897068280401000701a0a01005c6000e035140a0100118100e0e41a0200800380d708280401000401a6701004001906070140200800541c2d028040100260380d0500400a5
| 20 => 0x1c8280401000701a0a5c0080200080701a5c00801301c068280200158280401001e03270082141a0a01000f81c068280401001e10a1c069e8140200040380d3680802000e034140200264181c050091000080701a020009dd6100e034040100088380d050080200750701a0a01001d01c7383414020080038e60500400da4c030380d0500400e5060714c0a01004001c
| 21 => 0x701a0a1a80400220e03414ef0080050420e03414020080038ed06828040100198380d4802802000e034140200801d83a1c834140200800380d0482804000caf4380d050080027060701401000a0f01c0e8340401001c038111a034140200870140200800c8481d0401a6701004000c0e2101401000a0380d050040091140701a5c0500400280e0341402008b41834
| 22 => 0x1004001c4d0341402001c0181c0682804001384038840680800910e034140200801ee660e034140100294181c0682802007a840380d62008020006071e60a01004001c1a034b8010023c380d053c8040100030382f05008020078870680a01004001c0682804003e1e5e01c0682802006d0e8380d05008002706070680a00800503a0e0bc1402008001839068280401
| 23 => 0x6d0410a0d7a008001c06bf40401001c0380d7e0280401000701a0200800e8700e0d0b40a0100400100e03414022a000380d051780401000703a0d01004001c42028040100180201c0699c040013830380d0500400280e03414020009db41c7d034140200800380d052a802000e034140200801f21006b3c140200800201c1a0080200240701a0a7c00802000e210b40a
| 24 => 0x69b4040100070b40d0500802001d0701a0a81004001c0682a020200800380d05004002864070720a010040019330701a0a01001d01c1a034bc0200800201c068280468000701a6d80008020006070da020080020660e034b80100030380d04828040074870680d01004001c06a2804010018ccc850e03414ff000701a0a0100400fe0e0d01a021b000380d050040028
| 25 => 0x168401a0a0100400600e0d01a0a00800563a0e034b80200800181c8382804010007068d60500802000e0341402008020c1c1a028040100414380d050040028370401a67010040047748701a0a008014a1c0682804010018038e605004009808215080d05008001c06828020014088380d0500800278203038342e00802000e034b80a81804000c0e0280200358a0b61c
| 26 => 0x800e270068280401001d0c0e90e0341402003a03834248080200300401a670100400480e2541a0a01004001c06c301402008002034068080200300701b0a0500802000e034140200802121c038341402009c0380d050080027528701a0a010004e470e0e41a0a01000aa0c330719a0a00801800d0500802003c070d80d0500800270e034140200c203834068280401
| 27 => 0x3b8380a0100400480c84038340680802000e0781a0a01004000c0e028020014190200d0500800273e0701a7a0500800270e0341402008007c0c0e0d0040100322241c068280401000706802008003270080701a0200800f21c068280400138701a0a88004001c0682802001443c201c068280401000703c390682802005e8341402001f0380d868280401000301a02
| 28 => 0xe034140200154380d05460020006070680200800e00c0e3341401000a0387505008020056a14380d0500400280e0341402008022e1c0682a0401000701a0a0100401160e0341401000a0c6850e03414020009c741c068080200110701a0a0100401150e034140200800e81c8a034140200800380d050080200898701af44500802001d0701a0200801901c1a0340401
| 29 => 0x258181c390280401000701a920500802000e03414020009cf00c0e035440a00800380d50828040100040385a0680802000e0781a0a008001a02008004a1c0682804290e0341401000f8b61c068280401003ec380d0500400281c834140200800f01c06828040100350385a0500802003a0701a5c0100400480e0d0920200800e81c06828040048c64181c118280200
| 30 => 0x738280401000e81a0a0100400600e035e80a00800501c068296801003a4380d0500800270e034040100088421c06808020064120380d05004007c6a8701a0a01004011a060701a0a011a0001c1a02804010006438750500802003c0701a0a3780400280e0341401000a0f01c1a03414020009c201c06808020047a28140200800f019080701a0a010045a0c0e0341402
| 31 => 0x80700e0d05008020c0e0d0bc0200800741c1a12404010007022390682804010e0341401000f8e21c2e8341402008003839068280401000701a0a4e804007842871e60d05008001c06828020014438181c678280401000e8380d0500802000e078680d0500400100e034140200114380d052ac040100040380d01004011c0e0d01a0a01000ab1b0e034140200800181c
| 32 => 0xe0341402008019078080701a0200801221c069e8140200800f8100e034b80200800383406828040100368181c050080200320701a0a010040048428701a0a7f808001c06c78140200800181c190280401000701a0a01004011d06070680d0500802001d0701a0a010045a1c0682804010011c380200800581c1a034040100088720d0500802003a0706839248080200
| 33 => 0x42028040100198380d0500400da0e00802003218c380d0500802003c1c020850682804010036c380d050080200060719a0a01004001c1a124040100030380d05178040100030380d7a028040100070e40d050080200060701a0a0100400710e03414df0100400780e0340401001c4e010068280401001f0380d3d028040100070683906828040100198380d2e0280200
| 34 => 0x701acf050080200210701a0a01004001c068280200900701a0200ac8000c0e0341402008020a1c1a034140200800380a0100400b10e03414b801004001c068280401001e0380d0500802003c871ce0d050080200060701a0a1a80400100e03414020080032100e034040100321f61c068280401000701a0a01004011f060701a0a0100400280e0342a0a010043834
| 35 => 0x68280401003c4380d0500802000e034145e01004001c06828040100260e21c0e834040100214383406828040100030380d050040028748701a0a0100400100e034140200801b41c1a0280401001ac380d050086c000e03414670100400190e034140200801bc0c080701a0a01004000a0100400780c9990a1c068280401000701a0a010040078318e8201c068280401
| 36 => 0x701a0a6600802000e2101a0a0100400710e3581a0a01004001c0682804010041438d6068280401001f0201c0682804010011c3834068280401001e0380d0500400e50e0341402008021c1c1a034140200800f21c06828040100180181c06828ce0200800380d05008020014070b40d0500802000e2681a0a01001f6660e034140200801ec0c0e034140200801e01c
| 37 => 0x1004001c068241402000701a0a01488001c3a8280401000701a0a01004007408070680d01004001c0682a060200800201c06828040100260380d0500800270e034140200801dc100e034140200800201c06828040100120201c068280401001f0380d7a0280401001e1d2660e034140200800200d3380802000e034140200801621c0682a4202008010a1c06bd01402
| 38 => 0x500802000c830380d050080200640701a0a010040019384910a1c068280401000701a0a01004012608198380d0500802000e034152501004001c06828048800034140200801b4780e1941a0a0100401240e03414020080038e406828040100070b40d050080200388701a0a010040123080701a0200800e21c1a034140200800c00c0e034b80a010040010428701a0a
| 39 => 0x318701a0a0100400980e034140200800f83a0e0d01a0a01004001c0682804010011e22100e0341402008010a0d050080200388701a5c050040098060701a0a0100400630e0e41a0a01004001c0682804003e244741c068280401000701a0a0131802000e194680d0500802000e1d41a0a0100400100e034140200800e21c1a034140200800e81c0682804010049c3834
| 40 => 0x1c068280401000701a0a7f80802000e03414020080032100e034140200800380d190280401000701a0a01004006b0e034144901004001c06bd01402008003834068280401000701a0a0100400780e2101a0a0100400850e034140200800380d050080200
| _ => 0
def stOffB : Nat → Nat → Nat
| 3, 0 => 0x7100184005100104003100084001100004
| 4, 0 => 0x56d415650545414c5051d4142504f54138504cd412e504a541245047d411a5045541105042d41065040540fc503dd40f2503b540e85038d40de5036540d45033d40ca5031540c0502ed40b6502c540ac5029d40a25027540985024d408e502254084501fd407a501d54070501ad406650185405c5015d40525013540485010d403e500e54034500bd402a5009540205
| 4, 1 => 0x7ed41f6507c541ec5079d41e25077541d85074d41ce5072541c4506fd41ba506d541b0506ad41a650685419c5065d41925063541885060d417e505e54174505bd416a5059541605
| 5, 0 => 0xddd837160dad836560d7d835960d51434e60d21834260cf1833660cc1832a60c91831e60c61831260c31830660c0182fa60bd182ee60ba182e260b7182d660b4182ca60b1542bf60ae582b360ab582a760a85829b60a55828f60a258283609f58277609c5826b60999426060969825460939824860909823c608d98230608a9822460879821860849820c6081982006
| 5, 1 => 0x13d184ee613a184e26137184d66134184ca6131184be612e184b2612b184a661281849a61251848e612218482611f18476611c1846a61191845e61161845261131844751105843b610d5842f610a5842361075841761045840b6101583ff60fe583f360fb583e760f8583db60f5943d060f2983c460ef983b950ecd83ad60e9d83a160e6d839560e3d838960e0d837d6
| 5, 2 => 0x19cd866d6199d86616196d86556193d86496190d863d618dd8631618ad862561881461a61851860e618218602617f185f6617c185ea6179185de6176185d26173185c66170185ba616d185ae616a185a261671859661641858a61611857e615e18572615b1856661581855a61551854e615218542614f18536614c1852a61491851e6146185126143185066140184fa6
| 5, 3 => 0x77361db5876761d85875b61d55874f61d25874361cf5873761cc5872b61c95871f61c65871361c35870761c0586fb61bd586f051ba986e461b7986d861b4986cd51b1d86c161aed86b561abd86a961a8d869d61a5d869161a2d8685619fd86796
| 6, 0 => 0x2485c91a7244dc90c724198901523e9c8f3723b588e67237dc8d872345c8ca7230dc8bc722d5c8ae7229dc8a072265c8927222dc884721f5c876721bdc86962189c85b72151c84d72119c840620e98834620b5c8267207dc81962049c80b7201587fe71fddc7f161fa9c7e461f75c7d761f41c7ca61f0dc7bc71ed5c7ae71e9dc7a071e65c79451e35c78671e0187797
| 6, 1 => 0x2b55cace72b1dcac072ae5cab272aadcaa472a75ca9672a3dca8872a098a7b729d1ca6d7299d8a6072965ca527292dca44728f98a38628c5ca2a7288dca1d62859ca0f72821ca01727e9c9f4627b5c9e67278549da7274dc9cc72715c9be726ddc9b0726a5c9a27266dc99472635c986725fdc978725c5c96a72591895d72559c95062525c943624f1c936624bdc9287
| 6, 2 => 0x3241cc8973209cc7b731d1cc6d73199cc5f73161cc5173129cc43730f1cc36630bdcc2873085cc1a7304dcc0c730198bff72fe58bf272fadcbe472f75cbd672f3dcbc962f09cbbb72ed1cbad72e99cba062e65cb9272e2dcb8472df5cb7672dbdcb6872d85cb5a72d4dcb4c72d15cb3e72cddcb3072ca5cb2272c6dcb1472c35cb0672bfdcaf872bc5caea72b8dcadc7
| 6, 3 => 0x392d8e44738f5ce36738bdce2873885ce1a7384dce0c73815cdfe737ddcdf0737a5cde27376dcdd473735cdc6736fdcdb8736c5cdab636958d9e7365dcd90736298d83735f1cd75735b9cd6773581cd5973549cd4b73511cd3d734d9cd2f734a1cd2173469cd1373431cd06633fdccf8733c5ccea7338dccdc73355ccce7331dccc0732e5ccb2732b18ca573279cc977
| 6, 4 => 0x4001cff973fc9cfeb73f91cfdd73f59cfcf73f21cfc173ee9cfb373eb1cfa573e79cf9773e41cf8973e09cf7b73dd1cf6d73d9d8f6073d65cf5273d2dcf4473cf5cf3673cbdcf2873c85cf1a73c4dcf0c73c15cefe73bddcef073ba5cee273b6dced473b398ec953b114ebe63addceb073aa5cea273a6dce9473a35ce8673a018e7a639d18e6d73999ce5f73961ce517
| 6, 5 => 0x102174069d01554039d0077
| 7, 0 => 0x47b5d1e58477d91d784741d1c97470611ba746d191ac84695d19d8465d918f8461e117f845e1d171745ad916564576115674541914974509d13b744d1d12d74496111e7445dd110744221102643edd0f4743b990e68437dd0d874345d0cb6430e10bb842d1d0ac84292109d74259d08f7421e1080741e21071741a610627416a105374131d045740f9d037740c1d0288
| 7, 1 => 0x4ef5d3b674ebdd3a874e82139974e46138984e09d37b74dce136b84d8e135c74d52134d74d1d934074ce5d33274cadd32384c71d31574c36130584bf612f764bc592eb64b91d2dd74b59d2ce84b2192c174ae9d2b284aaa12a284a6a129464a35d286749fdd278749c2126974989d25a8494a124a84911923d748d6122e7489a121f74861d2126482a1202847edd1f47
| 7, 2 => 0x4fa613e274f6a13d374f31d3c48
| 8, 0 => 0x5131d445750f9d437750c1d42975089d41b75051d40d75019d3ff74fe1d3f17
| 9, 0 => 0x14536
| _, _ => 0
def readSt : Nat → Nat → List Nat
| 0, _ => []
| n + 1, p => wireSAt (fld (stPool (p / 128)) 9 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
| 0 => 0x68280e0d3068290608f190090e0350e0340e0290e035338050e0280600b060cb0e0350e03408035338050e0290e0280e029068050e00506829410010091f080360e029050ab060cb0e0350e0340602a190090e0350e0340600b0e035190010e034068291b001080040e0290e0290e035190010e034080070819f0e0290e0280e0351a0090e009050350e0b03218d0682b0682a068290e0291a801060080e035
| 1 => 0x10870602a0e0350e0291c8050e0d0068290819f0e028080360e029190a20600b0e0350e0340e0350e029338090e028190010e034060290e0350819f0e028080350e029080351b001080040e0291c8050e0d00e029068291d127068280e0d106829010aa3c0650e0370e0360e0293c0650e0370e0360e0291a801060080e035051e13c0650e0370e0360e1941a0090e00905035008960819f0e0290e028249d1
| 2 => 0x1a00b05035068880602b0e03500921080370e0290e029338010e0280600b0e0350e0280e24506805050070e0d00e035050350e035190290e034050a9060cb0e0350e0340e0b11a12706829068281a127068280e0d006829008960819f0e0290e0281a127068280e0d1068295a0012d008069c50e02b068291b001080040e0290e029060080e03505035080371b001080040e029190010e0340602a0e03555001
| 3 => 0xe1d606b210500b1a0670e036050350123d1a00b050350600b0e0350e034011c50e02b06809080040e0350e0290819f0e0290e0280132b069c40e02b1b001080040e02908004080350e0290e035190010e034009910e0290503606b190e24705007068290e125068280e0340e0290e03562009050670e036389c10e02b0e02a1a1f00e00706829010850602a0e0350600b0e0350e0090e0850602a0e0350e23f
| 4 => 0xe02b01379051e00e0371a12706829068281c8290e0d0068290e029338090e0280800b0e029050090e0370e0d20503548037053690e00b06829060280e0356c0010118f0682a050070e0290e0076b00b069f10e0073c0650e0370e0360e1d706b210500b068a00600b0e0350e0290e007068291d0040e0d106829051f10e00706829050090e009050352d007069c50e02b0e1930e02b05036010870602a0e035
| 5 => 0xe171050090680b06b690e00b0e0353380a0e0280e035052610680b0680b0e0350e00b0e0350533506809190090e0350e0340e0290e00506829068050e02b0e005069c70e02b0682906a450e035050071d0070e0d1068290e1d406b210500b45007051e10e037053890e1af06807060cb0e0350e0340680b069c50e02b1a3690e00b05035060080e035050350e036051e30e0370e029338350e0280e02a069c5
| 6 => 0x60080602b0e035008a10600b0e03506bb94282b0e005338050e0280e0365e8070e245050070e0370600b0e0350682b080370e0290e028080350e0290600b0e035068050600b0e03505007050090600b0e035050090e0290680b1d00b0e0d105035428070e0290e0050e120080370e029051f10e0070e005051ad0e0290680748007053690e00b009910e035050360509e080070e0290e0290602b0e03574807
| 7 => 0xe03506829069c50e02b0091d080360e029050bd080340e029068050e0d2068297d80b060090e035080070e0290e00b2d005069c50e02b010870602a0e0353c1c10e0370e02a06805069c50e02b0e02a190050e0340e02906805050077480b330290e0097b00b060050e0350e029050670e0360e03506bd105005050091a00b05035068290e1ad068070e2610e00b0680b08007080350e0290600b0e03505035
| 8 => 0x80070e0290e0350503505009011e10e037050090e1b5051ad06807068890602b0e0351d0080e0d1050350e0d00e0360503574807330290e00906829060280e0351d004080350e0290e1b4051ad068070e035051ad068070e0090e029050090e035338050e028330290e00905035051e10e0370682a010050e0090e005080040e029068290e00b0600b0e0350e0050e029050050e02a050650e036050a10600b
| 9 => 0xe02a0e0350e02b748070e17105009068280e0d2068290e19405335068090542d428370e005011820e0d2050350e02a190010e0341c8060e0d0068290e0090e035068090e18d0e0370682a0689d080070e02900329069c40e02b0e0290e0d206829080350e02905009061930e03505036069f10e00706829060070e035050350e028080360e0297480b0e171050090680b06b690e00b0e0290e005068050109e
| 10 => 0x682a0e005080070e029060290602b0e035641e10e0370500b05005051e10e037060290e0350500b4282b0e005068290e036080370e029051c50e02b068290600b0e035050360e09c080070e0293d007051f10e007068290e0350500b082610e0290680b0e02a0e036050350e0291a00706829888070e3d10500501329069c40e02b0e229051e10e0371c8090e0d0050350e2450e00705007054390e33706809
| 11 => 0x60280e0350e035338090e0280e298052610680b1c8090e0d0050350819f0e0290e0281b001080040e0292d00b069c50e02b081ad0e029068077d80b0e335068090e0d00e037050350e1d706b210500b069d10e0d30503505009080370e0290e035190090e0341c8060e0d0068290137b051e00e0370e0350e02a068290600b0e035068090600b0e0350e0050e39306a45050071d0080e0d1050350600b0e035
| 12 => 0xe1930e0350503606921080370e0291d007080350e029063230e0350500b0e4711902a0e0341c8060e0d006829888350e3d105005068850602a0e0350e0d10e0d2068290600b0e035050052d008069c50e02b08009080070e0296b00b069f10e0071d004060290e035069800e0d2050350e03706b210500b060370600b0e035080070e029068290e0291a00b050350e036051e10e0370e035338060e02806979
| 13 => 0xe0070e029050090e00b050350e03505036080370e0290e00501005069c30e02a0e0350e0343302b0e0090e035050351d0030e0d106829080360e1c10e02a3218d0682b0682a050350602b0e0350e1d30e0d306829068280e0d0068290e029190010e03406829060280e035068280e0d1068291c8010e0d006829330d00e009050351a1830e0d2068290118d0e0370682a1a0050e00506829068a20600b0e035
| 14 => 0xe028069c70e02b0e0cb0e0341a00706829069c10e02a060080e0350e0290e0360e0290500b0e335068094280b0e0050600b0e035338010e02806829068050e00b0e0090682b0682a0e0370e02a0e0290e0050e191050360e035068090682906828060280e0350e03505005338350e0280e0350e02b051e30e0370e02b0e02a0e0290e007051f10e0070e0d0068290e009050090e0370500b0e02905007051f1
| 15 => 0x68091a007068290e0d2068290e0350e0280600b0e035069c50e02b190050e034330350e009060050e0350e2610680b0e1ad06807060280e0350e02b0680b190290e0340e005068290600b0e0350e171050090e0290e00b0680706829080040e0290e0280e036051e00e0370e0370e0360e0090e0050e0370682a080350e0290e193050360e125068281900a0e034051af06807060070e0350698d0682a33836
| 16 => 0x5007069c50e02b0e12706828051c50e02b0e0d2068290e035050090e0290e005338050e028009930503606b210500b0e0d3068290e02906829011e10e0370e0290680b080070e0294282b0e0050e1c10e02a0e0290e0070e03705005330290e0090e0290e028338360e0280e3230500b0e00505005011c50e02b0e02b06805069f10e007060070e035069f10e007080360e0290e037050353380a0e0280e337
| 17 => 0xe0360e0290e034068070682805005068290e037068050e0050682a0680b0e0070e0d106829080360e029080050e0290e02b0e005050090680b0e0350682a0e0d0068290e007050070e0d1068290e247050071a0090503506b210500b051c50e02b0e3ff010050e036050350e0350500b0e02a0e036428090e0050e173050090e0290e009011f10e00700991050360e0370e00b05335068090e3fd0100506a45
| 18 => 0x1005
| _ => 0
def opOffB : Nat → Nat → Nat
| 4, 0 => 0x5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
| 4, 1 => 0x0
| 5, 0 => 0xa500000000000000009500000000000214000000000007500000000000000000000000000000000000000000000000000000000000000000000000000000006500000000000000000000000000000000005500000004500000000000000000000000003500000000000000002500000000000054000000000000000000000000000000000000000000000
| 5, 1 => 0x55400000051400000000000000000000000000001350000000000000000000000000000000001250000001150000000000000000000000000000000000000041400000000000000000000000000000000000000000000000000000000f50000000000000000000000000e50000000000000000d50000000000000000000000000c5002d4000000000000000000
| 5, 2 => 0x205000000000000000000000000000007d400000000000000000000000000001e50000000000000001d50000001c5000000000000000000000000000000000000000000000000000000006d40000000000000000000000000000000000000000000000000000000000000000000006940000000000000000000000000000195006140000005d4000000000000000594
| 5, 3 => 0xa54000000a140000000000000000000000000000275000000000000000000000000265009540000000000000009140000000000000000000000008d4000000000000000000000000000000000000000000000000000894000000854
| 6, 0 => 0x12a3000000000049cc12430484c11e3046cc00000460c1153000000000000001123043cc10c30424c10630000010330400c0fd303e8c0f73000000f4303c4c000003b8c0000000000eb303a0c0e530000000000388c0df30370c0d930358c0000034cc0d03000000000000000cd30328c0c730310c0c1302f8c000002ecc000002e0c0b5302c8c0af302b0c0a93
| 6, 1 => 0x6d0c1b1306b8c0000000001ab306a0c1a530688c19f30000000000000019c30664c00000658c19330640c18d30628c18730610c18130000017e30000017b305e0c17530000017230000016f305b0c16930598c16330580c15d30568c0000055cc00000550c00000544c14e30000014b30520c14530508c000004fcc13c300000139304d8c133304c0c12d3
| 6, 2 => 0x8ecc238300000235308c8c22f300000000008b0c22930898c22330880c21d30868c21730850c21130838c0000082cc20830814c202307fcc000007f0c1f93000001f6307ccc000007c0c1ed307a8c1e730790c00000000000000784c1de3000001db3000001d830754c1d23073cc1cc30000000000724c00000718c1c330700c0000000001bd306e8c000006dcc0000
| 6, 3 => 0xb08c00000afcc2bc30ae4c2b63000000000000002b330ac0c2ad30aa8c2a73000002a430a84c29e30000029b30a60c29530a48c28f30a30c00000a24c28630a0cc280309f4c000009e8c277300000274300000000009c4c26e309acc00000000026830994c2623097cc25c3000002593000002563094cc25030000024d30000024a3091cc00000910c24130000023e3
| 6, 4 => 0xd6cc35830d54c35230d3cc00000d30c34930d18c34330d00c33d30ce8c00000cdcc33430cc4c32e30cacc32830c94c32230c7cc31c30000000000c64c00000c58c31330c40c00000c34c30a30c1cc30430000030130bf8c0000000002fb30be0c00000bd4c2f230bbcc2ec30ba4c2e630b8cc2e030b74c2da30000000000b5cc2d430b44c2ce30b2cc00000b20c2c53
| 6, 5 => 0x36a30d9cc36430d84c35e3
| 7, 0 => 0xfa483e720f9483e320f8483df20f7483db20f6483d720f54800000f4c83d120f3c83cd20f2c83c920f1c83c520f0c83c120efc83bd20eec83b920edc83b520ecc83b120ebc83ad20eac83a920e9c83a520e8c83a120e7c839d20e6c839920e5c839520e4c839120e3c838d20e2c838920e1c838520e0c838120dfc837d20dec837920ddc837520dcc837120dbc836d2
| 7, 1 => 0x1194846321184845f21174845b2116480000115c84552114c84512113c844d2112c84492111c84452110c8441210fc843d210ec8439210dc8435210cc8431210bc842d210ac84292109c84252108c84212107c800001074841b21064841721054841321044840f21034840b2102484072101484032100483ff20ff483fb20fe483f720fd483f320fc483ef20fb483eb2
| 7, 2 => 0x11c4846f211b4846b211a484672
| 8, 0 => 0x1200447f111f8447d111f0447b111e84479111e04477111d84475111d044731
| _, _ => 0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
| 0, _ => []
| n + 1, p =>
  let code := fld (opPool (p / 64)) 20 (p % 64)
  (code &&& 3, wireSAt ((code >>> 2) &&& 511), wireSAt ((code >>> 11) &&& 511)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 18 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
| 3, 0 => 0x0
| 4, 0 => 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
| 4, 1 => 0x0
| 5, 0 => 0x40000000000000000080080000000000040000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000002020000000000000000000000000000000000040000000010000000000000000000000000000005800000000000000010000000000000088400000000000000000000000000000000000000000000000
| 5, 1 => 0x40000000800000000000000000000000000000001100000000000000000000000000000000000004000000000400000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000004000000000000000000000000020020000000000000000400000000000000000000000000000a002210000000000000000000
| 5, 2 => 0x200000000000000000000000000000000100000000000000000000000000000000000080000000000000000100000002000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000006004000000000000000000000000000000442080040000000010000000000000000008
| 5, 3 => 0x18010000000020000000000000000000000000000000452000000000000000000000000001000221000000000000004020000000000000000000000000042010000000000000000000000000000000000000000000000000000008000000000020
| 6, 0 => 0x1000000000000013000a80010000040308e000000002080100000000000000000002000400200008000002000000000640802000080200004810000000015020000000010000000000000008940000b48000000000000100081c46010100080001108000001000000240000000000000000994101080001120000002000020000000400000000010003260000202000000080040
| 6, 1 => 0x20000020002000000000000008004420200800010020000000000000000002000000200000003000010000c0000480002810010004000004000000001000000001000220000400000240440000002040300600008040000008004000000c00128000000004000000001000000200000010000002001004000010001108000000080001040000002270300200194000200010
| 6, 2 => 0x4080080000000000200400080040000000000002000010000400022020060400401000024004000000800040000000101e0001120008000804002000000100000020000000044000100000020080001010000000d0004000000000000000000040010000000080000000200100402000200004400010000000000000400000008000080100008000000000002000000400000100000000
| 6, 3 => 0xa00000000804022000020002000000000000000000080002008000002000080000000004000500000800000000401002000200001000010008200000001000001000420800001000000000004000200000022010000000000000100200000800000000000202112000000400000804400000000004000000004000200808800000002200000000804100800001002202080000000004
| 6, 4 => 0x4420210001000022100002000000800000010003000080080000010030020000000010000c00040000801000802000000200008010280080000000000000010000004000000200004000000002000020000200840000000090001000000000000009000402800000000200895b002000010000424004000880004000020001000000000003086000040000802080202800000000100002
| 6, 5 => 0x1000400089c000400001
| 7, 0 => 0x466008500c23808220002ea40042120010374c04e06104013480000030ae300180804000010301e008c40523810370c004008cc013b8184b0308e0809c01188a20501010200945101a60071202800d981014850050047e00121200081809140020089c010002022004ee20100002400269400c68212c0000a9001020101082c0030280010240006064000fa68030046606145480181000
| 7, 1 => 0x3e0082c000384a07024080409c0014000004c00a060340804000181810ca400d40002a2030340a041541103ae0010140620100011b8c009000300481020110026d0206e000bc00038001f14482028400107a4807004c20000000300082250000008bc013b8902748002a41040411020630404e08148040000018020de2880c00150001f004820880c002f818451200818008050281033
| 7, 2 => 0x81813080449018c050081008
| 8, 0 => 0x1110381803400060615c081980233410560888c700b820234c00e008cc0503aa827
| 9, 0 => 0x7
| _, _ => 0
def PM (s j : Nat) : Nat := fld (pmB s (j / 64)) 19 (j % 64)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_62, 8, runOps true dom_62 (0, roots_62) ops)] else []) ++ (if pm.testBit 1 then [(dom_61, 7, runOps true dom_61 (0, roots_61) ops)] else []) ++ (if pm.testBit 2 then [(dom_59, 7, runOps true dom_59 (0, roots_59) ops)] else []) ++ (if pm.testBit 3 then [(dom_55, 6, runOps true dom_55 (0, roots_55) ops)] else []) ++ (if pm.testBit 4 then [(dom_47, 6, runOps true dom_47 (0, roots_47) ops)] else []) ++ (if pm.testBit 5 then [(dom_53, 5, runOps true dom_53 (0, roots_53) ops)] else []) ++ (if pm.testBit 6 then [(dom_31, 5, runOps true dom_31 (0, roots_31) ops)] else []) ++ (if pm.testBit 7 then [(dom_57, 5, runOps true dom_57 (0, roots_57) ops)] else []) ++ (if pm.testBit 8 then [(dom_54, 5, runOps true dom_54 (0, roots_54) ops)] else []) ++ (if pm.testBit 9 then [(dom_51, 5, runOps true dom_51 (0, roots_51) ops)] else []) ++ (if pm.testBit 10 then [(dom_46, 5, runOps true dom_46 (0, roots_46) ops)] else []) ++ (if pm.testBit 11 then [(dom_45, 5, runOps true dom_45 (0, roots_45) ops)] else []) ++ (if pm.testBit 12 then [(dom_43, 5, runOps true dom_43 (0, roots_43) ops)] else []) ++ (if pm.testBit 13 then [(dom_41, 4, runOps true dom_41 (0, roots_41) ops)] else []) ++ (if pm.testBit 14 then [(dom_29, 4, runOps true dom_29 (0, roots_29) ops)] else []) ++ (if pm.testBit 15 then [(dom_27, 4, runOps true dom_27 (0, roots_27) ops)] else []) ++ (if pm.testBit 16 then [(dom_52, 4, runOps true dom_52 (0, roots_52) ops)] else []) ++ (if pm.testBit 17 then [(dom_49, 4, runOps true dom_49 (0, roots_49) ops)] else []) ++ (if pm.testBit 18 then [(dom_42, 4, runOps true dom_42 (0, roots_42) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool :=
  (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_63 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact cpcs (by decide +kernel) lowS_62 _ g hchk
    · exact cpcs (by decide +kernel) lowS_61 _ g hchk
    · exact cpcs (by decide +kernel) lowS_59 _ g hchk
    · exact cpcs (by decide +kernel) lowS_55 _ g hchk
    · exact cpcs (by decide +kernel) lowS_47 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53 _ g hchk
    · exact cpcs (by decide +kernel) lowS_31 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57 _ g hchk
    · exact cpcs (by decide +kernel) lowS_54 _ g hchk
    · exact cpcs (by decide +kernel) lowS_51 _ g hchk
    · exact cpcs (by decide +kernel) lowS_46 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43 _ g hchk
    · exact cpcs (by decide +kernel) lowS_41 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27 _ g hchk
    · exact cpcs (by decide +kernel) lowS_52 _ g hchk
    · exact cpcs (by decide +kernel) lowS_49 _ g hchk
    · exact cpcs (by decide +kernel) lowS_42 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_62 8 s (0, roots_62) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_63 goalM v ys :=
  checkRootSub_sound (by decide +kernel) lowS_62 h
def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c, 2), (0xff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_63 goalM v ys) : RunD true dom_63 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s : Nat) := barP true dom_63 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true :=
  span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 45 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 45 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z4_45 : ∀ i, 45 ≤ i → i < 90 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 45 45 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z4_90 : ∀ i, 90 ≤ i → i < 96 → Z 4 i = true :=
  span_ok (by decide +kernel : span (Z 4) 6 90 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 96 → Z 4 i = true :=
  range_split (z4_0) (range_split (z4_45) (z4_90))
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 45 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 45 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5_45 : ∀ i, 45 ≤ i → i < 90 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 45 45 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5_90 : ∀ i, 90 ≤ i → i < 135 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 45 90 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5_135 : ∀ i, 135 ≤ i → i < 180 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 45 135 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5_180 : ∀ i, 180 ≤ i → i < 225 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 45 180 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z5_225 : ∀ i, 225 ≤ i → i < 235 → Z 5 i = true :=
  span_ok (by decide +kernel : span (Z 5) 10 225 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 235 → Z 5 i = true :=
  range_split (z5_0) (range_split (z5_45) (range_split (z5_90) (range_split (z5_135) (range_split (z5_180) (z5_225)))))
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 45 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_45 : ∀ i, 45 ≤ i → i < 90 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 45 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_90 : ∀ i, 90 ≤ i → i < 135 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 90 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_135 : ∀ i, 135 ≤ i → i < 180 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 135 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_180 : ∀ i, 180 ≤ i → i < 225 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 180 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_225 : ∀ i, 225 ≤ i → i < 270 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 225 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_270 : ∀ i, 270 ≤ i → i < 315 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 45 270 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z6_315 : ∀ i, 315 ≤ i → i < 325 → Z 6 i = true :=
  span_ok (by decide +kernel : span (Z 6) 10 315 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 325 → Z 6 i = true :=
  range_split (z6_0) (range_split (z6_45) (range_split (z6_90) (range_split (z6_135) (range_split (z6_180) (range_split (z6_225) (range_split (z6_270) (z6_315)))))))
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 45 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 45 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z7_45 : ∀ i, 45 ≤ i → i < 90 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 45 45 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z7_90 : ∀ i, 90 ≤ i → i < 134 → Z 7 i = true :=
  span_ok (by decide +kernel : span (Z 7) 44 90 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 134 → Z 7 i = true :=
  range_split (z7_0) (range_split (z7_45) (z7_90))
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 14 → Z 8 i = true :=
  span_ok (by decide +kernel : span (Z 8) 14 0 = true)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true :=
  span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, bar true dom_63 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi
  change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true
  rw [← barP_eq]; interval_cases s
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
  scr true dom_63 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_63 roots_63 goal_63 10 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_63
theorem lowS_63 : Lower true dom_63 roots_63 goal_63 10 := S_63.noCircuit



namespace GateElim

abbrev X := Fin 8 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 8) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 8) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 8) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 8) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 8} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 8} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 8) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 8) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 8) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2


def target : F := fun x =>
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) ||
  (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) ||
  (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)

def g1 : F := rs 6 false (rs 3 false target)

def emb6 (r : Nat) : X := fun i =>
  match i.val with
  | 0 => r.testBit 0
  | 1 => r.testBit 1
  | 2 => r.testBit 2
  | 4 => r.testBit 3
  | 5 => r.testBit 4
  | 7 => r.testBit 5
  | _ => false

def enc6Aux : Nat → F → Nat
  | 0, _ => 0
  | n + 1, f => enc6Aux n f ||| (if f (emb6 n) then 1 <<< n else 0)

def enc6 (f : F) : Nat := enc6Aux 64 f

theorem enc6Aux_bit (f : F) (n r : Nat) :
    (enc6Aux n f).testBit r = if r < n then f (emb6 r) else false := by
  induction n with
  | zero => simp [enc6Aux]
  | succ n ih =>
    simp only [enc6Aux, Nat.testBit_or, ih]
    by_cases hlt : r < n
    · have hne : r ≠ n := by omega
      have h1 : (if f (emb6 n) = true then 1 <<< n else 0).testBit r = false := by
        cases f (emb6 n) <;> simp [Nat.testBit_shiftLeft, show ¬ n ≤ r by omega]
      simp [hlt, Nat.lt_succ_of_lt hlt, h1]
    · by_cases heq : r = n
      · subst heq
        have h1 : (if f (emb6 r) = true then 1 <<< r else 0).testBit r = f (emb6 r) := by
          cases f (emb6 r) <;> simp [Nat.testBit_shiftLeft]
        simp [hlt, h1]
      · have hgt : ¬ r < n + 1 := by omega
        have h1 : (if f (emb6 n) = true then 1 <<< n else 0).testBit r = false := by
          cases f (emb6 n)
          · simp
          · simp only [ite_true, Nat.testBit_shiftLeft]
            have hb : (1 : Nat).testBit (r - n) = false := by
              rw [Bool.eq_false_iff, ne_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
              omega
            simp [hb]
        simp [hlt, hgt, h1]

theorem enc6_bit (f : F) (r : Nat) :
    (enc6 f).testBit r = if r < 64 then f (emb6 r) else false :=
  enc6Aux_bit f 64 r

theorem dom63_bit (r : Nat) : dom_63.testBit r = decide (r < 64) := by
  have heq : dom_63 = 2 ^ 64 - 1 := rfl
  rw [heq, Nat.testBit_two_pow_sub_one]

theorem enc6_mask (f : F) : enc6 f &&& dom_63 = enc6 f := by
  apply Nat.eq_of_testBit_eq; intro r
  rw [Nat.testBit_and, enc6_bit, dom63_bit]
  by_cases h : r < 64 <;> simp [h]

theorem enc6_const (b : Bool) : IsConst dom_63 (enc6 (fun _ => b)) := by
  cases b
  · left; apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, enc6_bit]; by_cases h : r < 64 <;> simp [h]
  · right; apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, enc6_bit, dom63_bit]; by_cases h : r < 64 <;> simp [h]

theorem enc6_not (f : F) : enc6 (fun x => !f x) = negD dom_63 (enc6 f) := by
  apply Nat.eq_of_testBit_eq; intro r
  rw [enc6_bit, negD, Nat.testBit_and, Nat.testBit_xor, enc6_bit, dom63_bit, mask256_bit]
  by_cases h : r < 64 <;> simp [h]

theorem enc6_comb (t : Bool) (a b : F) :
    enc6 (comb t a b) = opD dom_63 (if t then 0 else 1) (enc6 a) (enc6 b) := by
  apply Nat.eq_of_testBit_eq; intro r
  cases t
  · simp only [comb, opD, orD, enc6_bit, dom63_bit, Nat.testBit_and, Nat.testBit_or,
      Bool.false_eq_true, ite_false, show (1 == 0) = false from rfl, show (1 == 1) = true from rfl, ite_true]
    by_cases h : r < 64 <;> simp [h]
  · simp only [comb, opD, andD, enc6_bit, dom63_bit, Nat.testBit_and,
      ite_true, beq_self_eq_true]
    by_cases h : r < 64 <;> simp [h]

theorem enc6_av {s : Set F} {bank : List Nat}
    (hs : ∀ u ∈ s, Avail true dom_63 bank (enc6 u)) {f : F} (h : Av s f) :
    Avail true dom_63 bank (enc6 f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl (enc6_const b)
  · exact hs _ hu
  · rw [enc6_not]
    exact avail_neg (by decide +kernel) (hs u hu)

theorem prog_to_natReach {s : Set F} {f : F} {k : Nat} (p : Prog s f k) :
    ∀ {p0 : Nat} {bank : List Nat},
      NatReach true dom_63 roots_63 p0 bank →
      (∀ u ∈ s, Avail true dom_63 bank (enc6 u)) →
      ∃ bank', NatReach true dom_63 roots_63 (p0 + k) bank' ∧ Avail true dom_63 bank' (enc6 f) := by
  induction p with
  | done h =>
    intro p0 bank hr hs
    exact ⟨bank, hr, enc6_av hs h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro p0 bank hr hs
    set op := if tag then 0 else 1
    have hop : allowedB true op = true := by cases tag <;> decide
    have ha' := enc6_av hs ha
    have hb' := enc6_av hs hb
    set z := opD dom_63 op (enc6 a) (enc6 b)
    have hr1 : NatReach true dom_63 roots_63 (p0 + 1) (z :: bank) :=
      ⟨bank, enc6 a, enc6 b, op, hop, rfl, hr, ha', hb'⟩
    have hs1 : ∀ u ∈ insert (comb tag a b) s, Avail true dom_63 (z :: bank) (enc6 u) := by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · rw [enc6_comb]
        exact Or.inr (Or.inl ⟨z, List.mem_cons_self, rfl⟩)
      · exact avail_cons z (enc6 u) (hs u hu)
    obtain ⟨bank', hr', ha'⟩ := ih hr1 hs1
    refine ⟨bank', ?_, ha'⟩
    rwa [Nat.add_assoc, Nat.add_comm 1 k] at hr'

theorem enc6_x0 : xs64.getD 0 0 &&& dom_63 = enc6 (fun x => x 0) &&& dom_63 := by decide +kernel
theorem enc6_x1 : xs64.getD 1 0 &&& dom_63 = enc6 (fun x => x 1) &&& dom_63 := by decide +kernel
theorem enc6_x2 : xs64.getD 2 0 &&& dom_63 = enc6 (fun x => x 2) &&& dom_63 := by decide +kernel
theorem enc6_x3 : enc6 (fun x => x 3) &&& dom_63 = 0 := by decide +kernel
theorem enc6_x4 : xs64.getD 3 0 &&& dom_63 = enc6 (fun x => x 4) &&& dom_63 := by decide +kernel
theorem enc6_x5 : xs64.getD 4 0 &&& dom_63 = enc6 (fun x => x 5) &&& dom_63 := by decide +kernel
theorem enc6_x6 : enc6 (fun x => x 6) &&& dom_63 = 0 := by decide +kernel
theorem enc6_x7 : xs64.getD 5 0 &&& dom_63 = enc6 (fun x => x 7) &&& dom_63 := by decide +kernel

theorem stock_enc6 : ∀ u ∈ stock, Avail true dom_63 roots_63 (enc6 u) := by
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  match i, hi with
  | 0, _ => exact Or.inr (Or.inl ⟨xs64.getD 0 0, by simp [roots_63], enc6_x0⟩)
  | 1, _ => exact Or.inr (Or.inl ⟨xs64.getD 1 0, by simp [roots_63], enc6_x1⟩)
  | 2, _ => exact Or.inr (Or.inl ⟨xs64.getD 2 0, by simp [roots_63], enc6_x2⟩)
  | 3, _ => exact Or.inl (Or.inl enc6_x3)
  | 4, _ => exact Or.inr (Or.inl ⟨xs64.getD 3 0, by simp [roots_63], enc6_x4⟩)
  | 5, _ => exact Or.inr (Or.inl ⟨xs64.getD 4 0, by simp [roots_63], enc6_x5⟩)
  | 6, _ => exact Or.inl (Or.inl enc6_x6)
  | 7, _ => exact Or.inr (Or.inl ⟨xs64.getD 5 0, by simp [roots_63], enc6_x7⟩)
  | _ + 8, h => omega

theorem enc6_g1 : enc6 g1 &&& dom_63 = goal_63 &&& dom_63 := by decide +kernel

theorem low_g1 : Low 10 g1 := by
  intro k p
  obtain ⟨bank, hr, ha⟩ := prog_to_natReach p (p0 := 0) (bank := roots_63) rfl stock_enc6
  rw [Nat.zero_add] at hr
  exact lowS_63 k bank hr (avail_of_eq enc6_g1 ha)

theorem g1_eq_true : rs 6 false (rs 3 true target) = g1 := by
  funext x
  simp [g1, rs, target]

theorem low_r3f : Low 11 (rs 3 false target) :=
  one 6 false (good_at 2 17 0 (by decide +kernel)) low_g1

theorem low_r3t : Low 11 (rs 3 true target) :=
  one 6 false (good_at 0 17 0 (by decide +kernel)) (g1_eq_true ▸ low_g1)

theorem low_target : Low 13 target :=
  two 3 (good_at 64 17 0 (by decide +kernel)) (good_at 64 17 0 (by decide +kernel)) low_r3f low_r3t

def witGates : List Gate :=
  [⟨.or, [1, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [6, 10]⟩,
   ⟨.and, [7, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [13, 14]⟩,
   ⟨.or, [0, 2]⟩, ⟨.or, [16, 7]⟩, ⟨.and, [5, 17]⟩,
   ⟨.or, [11, 12]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [19, 20]⟩]

theorem wit_mono : ∀ g ∈ witGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem wit_eval : ∀ x : X, Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem graph_eq : ∀ x : X,
    decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = target x := by
  decide +kernel

theorem main : ∀ (gates : List Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2,
        (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧
        (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) →
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2,
          (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧
          (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ hev
  by_cases hlen : gates.length ≤ 13
  · exact ⟨gates, o, all_not_not low_target gates o hg hlen (fun x => (hev x).trans (graph_eq x)), le_rfl, hev⟩
  · refine ⟨witGates, 21, wit_mono, ?_, fun x => (wit_eval x).trans (graph_eq x).symm⟩
    have hwl : witGates.length = 14 := rfl
    omega

end GateElim


end PEqualNP.Outside.L_meta_30546

theorem PEqualNP.Outside.L_meta_30546 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := PEqualNP.Outside.L_meta_30546.GateElim.main
