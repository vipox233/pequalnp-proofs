import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32169_aux.NatCore
def pn (a b : Nat) : Nat := a * 1000000000000000000 + b

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
  [(pn (pn (pn (pn 77194 726158210796949047) 323339125271902179) 989777093709359638) 389338608753093290),
   (pn (pn (pn (pn 92633 671389852956338856) 788006950326282615) 987732512451231566) 67206330503711948),
   (pn (pn (pn (pn 108980 789870415242751596) 221184647442685430) 573802955824978313) 20242741769072880),
   (pn (pn (pn (pn 115341 536360906404779899) 502576747487978354) 537254490211650198) 994186870666100480),
   (pn (pn (pn (pn 115790 322417210952336529) 717160220497262186) 272106556906860092) 653394915770695680),
   (pn (pn (pn (pn 115792 89210356248762697) 446947946071893095) 522863849111501270) 640965525260206080),
   (pn (pn (pn (pn 115792 89237316195417293) 883273301227089774) 477609353836086800) 156426807153786880),
   (pn (pn (pn (pn 115792 89237316195423570) 985008687907852929) 702298719625575994) 209400481361428480)]
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
def dom_255 : Nat := (pn (pn (pn (pn 115792 89237316195423570) 985008687907853269) 984665640564039457) 584007913129639935)
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_255 : Nat := (pn (pn (pn (pn 115792 89237316195417293) 883273301227083649) 395004697715577185) 884398984752835072)
def dom_251 : Nat := (pn (pn (pn (pn 6811 299366900952671974) 763824040465167839) 410862684739061144) 563765171360567055)
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]
def goal_251 : Nat := (pn (pn (pn (pn 6811 299366900952665697) 662088653784403663) 339072476906014286) 862379094771501568)
def dom_187 : Nat := (pn (pn (pn 369 241278552157691970) 323944487454585450) 436916535645638415)
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_187 : Nat := (pn (pn (pn 369 241278552157691630) 41577566516121987) 62027607408904704)
def dom_186 : Nat := (pn (pn (pn 123 80426184052563990) 107981495818195150) 145638845215212805)
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_186 : Nat := (pn (pn (pn 123 80426184052563649) 825614574879731686) 770749916978610176)
def dom_184 : Nat := (pn (pn (pn 24 616085236810512798) 21596299163639030) 29127769043042561)
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_184 : Nat := (pn (pn (pn 24 616085236810512457) 739229378225175566) 654238857986310144)
def dom_168 : Nat := (pn (pn 375605920881494 618277028187118172) 10162642900484353)
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_168 : Nat := (pn (pn 375605920881154 335910107248654708) 635555206837305344)
def dom_178 : Nat := (pn (pn 478912164140282350 156062184808631109) 533640618074767365)
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_178 : Nat := (pn (pn 478912164140282009 873695263870167646) 158751689854943232)
def dom_146 : Nat := (pn (pn 111505427 404487720399995908) 236278966371287045)
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_146 : Nat := (pn (pn 111505087 122120799461532444) 861671534603010048)
def dom_170 : Nat := (pn (pn 1878029604407473 91385140935590860) 50813214502421765)
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_170 : Nat := (pn (pn 1878029604407132 809018219997127396) 676205761259372544)
def dom_154 : Nat := (pn (pn 28656894842 953344142798948416) 723694357420770565)
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_154 : Nat := (pn (pn 28656894502 670977221860484953) 349086925635715072)
def dom_185 : Nat := (pn (pn (pn 73 848255710431538394) 64788897490917090) 87383307129127683)
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_185 : Nat := (pn (pn (pn 73 848255710431538053) 782421976552453626) 712494396072264192)
def dom_169 : Nat := (pn (pn 1126817762644483 854831084561354516) 30487928701453059)
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_169 : Nat := (pn (pn 1126817762644143 572464163622891052) 655880492638274048)
def dom_161 : Nat := (pn (pn 4384504913013 555855373869888538) 972881275987165187)
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_161 : Nat := (pn (pn 4384504912673 273488452931425075) 598273839923986432)
def dom_137 : Nat := (pn (pn 262357 704896043555330261) 822329893291033347)
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_137 : Nat := (pn (pn 262017 422529122616866798) 447722461522821632)
def dom_41 : Nat := 0x30300000303
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_41 : Nat := 0x30200000200
def dom_179 : Nat := (pn (pn (pn 1 436736492420847050) 468186554425893328) 600921854224302095)
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_179 : Nat := (pn (pn (pn 1 436736492420846710) 185819633487429865) 226032926004346880)
def dom_177 : Nat := (pn (pn 287347298484169410 93637310885178665) 720184370844860419)
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_177 : Nat := (pn (pn 287347298484169069 811270389946715202) 345295459804774400)
def dom_163 : Nat := (pn (pn 21922524565067 779276869349442694) 864406379935825935)
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_163 : Nat := (pn (pn 21922524564727 496909948410979231) 489798926692777984)
def dom_147 : Nat := (pn (pn 334516282 213463161199987724) 708836899113861135)
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_147 : Nat := (pn (pn 334515941 931096240261524261) 334229467345453056)
def dom_171 : Nat := (pn (pn 5634088813222419 274155422806772580) 152439643507265295)
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_171 : Nat := (pn (pn 5634088813222078 991788501868309116) 777832190264216064)
def dom_155 : Nat := (pn (pn 85970684528 860032428396845250) 171083072262311695)
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_155 : Nat := (pn (pn 85970684188 577665507458381786) 796475640477125120)
def dom_153 : Nat := (pn (pn 17194136905 772006485679369050) 34216614452462339)
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_153 : Nat := (pn (pn 17194136565 489639564740905586) 659609182667276800)
def dom_139 : Nat := (pn (pn 1311788 524480217776651309) 111649466455166735)
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_139 : Nat := (pn (pn 1311448 242113296838187845) 737042034686953984)
def goal_185_l144 : Nat := (pn (pn (pn 73 848255710431538394) 64788897490917090) 87383302834160128)
def goal_169_l128 : Nat := (pn (pn 1126817762644483 854831084561354516) 30487924406485504)
def dzo_185_2 : Nat := (pn (pn (pn 295 393022841726153576) 259155589963668360) 349533228516510732)
def gzo_185_2_144 : Nat := (pn (pn (pn 295 393022841726153576) 259155589963668360) 349533211336640512)
def goal_171_l130 : Nat := (pn (pn 5634088813222419 274155422806772580) 152439639212297740)
def dzo_171_16 : Nat := (pn (pn (pn 369 235644463344469551) 49789064647812870) 284476892138373120)
def gzo_171_16_130 : Nat := (pn (pn (pn 369 235644463344469551) 49789064647812870) 284195417144688640)
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
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn 210315346 606294972657576564) 209226864185732468) 46242640726015795) 554977636746456967) 690197588539769570) 511403067100033653) 466888018636803184) 996608884627996928)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn 340 282366841710300967) 557013907638845440), 96)], [((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24), ((pn (pn 338 958311018522360492) 699998064329424640), 120)], [((pn (pn 338 958311018522360492) 699998064329424640), 120), ((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn 338 958311018522360492) 699998064329424640), 120)]]
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
    [((pn (pn (pn 24 615709630889631303) 403319270976520858) 18965126142558208), 128, 144)] (by decide +kernel) (by decide +kernel) low_168

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
|0,0=>(pn (pn (pn (pn (pn (pn (pn 3549071 362179606317425596) 296605181185002222) 219285603106527163) 347831314079186452) 480193323425904904) 619377678253734443) 452165344626737156)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn 340 277174703306882242) 637262502835978240), 112)], [((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14), ((pn (pn 272 225893536750770770) 699685945414569164), 126)], [((pn (pn 272 225893536750770770) 699685945414569164), 126), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn 272 225893536750770770) 699685945414569164), 126)]]
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
    [((pn (pn 478912164028776922 751574464408635201) 297361651703480320), 128, 160)] (by decide +kernel) (by decide +kernel) low_146

theorem low_170 : Lower true dom_170 roots_170 goal_170 5 :=
  lower_slice (d:=dom_170) (dSub:=dom_168) (T:=goal_170) (TSub:=goal_168) (roots:=roots_170) (rootsSub:=roots_168)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 1502423683525978 473108112748472688) 40650571601937412), 128, 130)] (by decide +kernel) (by decide +kernel) low_168

theorem low_154 : Lower true dom_154 roots_154 goal_154 5 :=
  lower_slice (d:=dom_154) (dSub:=dom_146) (T:=goal_154) (TSub:=goal_146) (roots:=roots_154) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 28545389415 548856422398952508) 487415391049483520), 128, 136)] (by decide +kernel) (by decide +kernel) low_146

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
|4,0=>(pn 178662 607497660125461525)
|5,0=>(pn (pn (pn 452719 386009363522013429) 168696588966373191) 843801897112708158)
|6,0=>(pn 400633 656117887631398179)
|7,0=>0x54d66
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 5 45177009345705519) 367174996355646246) 226617012562091305) 69747436034496150) 970312616735408968) 445957855028642385) 310967896323448354) 394480944001944291) 319936415288676555) 617827150515579898) 641218635216772645) 475686678843119334) 120415402762028333) 930497594734103579) 114529345508383643) 698438004696347261) 756348988339257519) 551216717776460139) 951895584343762852) 329317750869264623) 43996289303085919) 415065496798355381) 887812399049873329) 913792022558704408) 898618855111725288) 712598442006916415) 613782668964706082) 982579049539416052) 356965485298943436) 627170859357392064) 520961043750919811) 174142349236598513) 171073410398360818) 929605977171399355) 453250349913073264) 504504918613706191) 371096147197164379) 935238855122079530) 143018353651022111) 410103318801665555) 778695121665668995) 256384052158751844) 756116984490602682) 549709514937730645) 249951292351389960) 227505622268589755) 601721238860266235) 836759207614937467) 553800401905038945) 108468641413029743) 237933992608978705) 420316201045079395) 344882816266567511) 644232608195036236) 391067946971029607) 666950483888248208) 586561792873176158) 236162113717109625) 444903180194989621) 569947248156262933) 455150859137761372) 56769781459420366) 627038445353720703) 513540777062509415) 675383072560064705) 65957366261073499) 382016432388489569) 811579334762117128) 98586242803889158) 363811147042709667) 702247288531107586) 259965084918471048) 868704129108139783) 125421233511744407) 284581012269863146) 908050158613275502) 197060227368470532) 724701648507634944)
|_,_=>0
def stPool : Nat → Nat
|0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn 19130 288836836419119054) 268774577384350448) 244586512268711687) 589716331962480898) 847837532946518858) 433549368589467840) 875426864729180886) 513563485185224767) 561865811747506208)
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>(pn 794541645240570 969245689419084166)
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
|0=>(pn (pn 292267550080160627 863632969287909511) 929264878470255247)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn (pn 360 442301127832514937) 185945552335899932) 357928920281911406) 871856833970831564), 6), ((pn (pn (pn 26959535291011 309494617955681309) 695723670668989160) 619180400863805440), 16)], [((pn (pn (pn (pn 360 442301127832514937) 185945552335899932) 357928920281911406) 871856833970831564), 6), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14), ((pn (pn (pn 21567957328698 830448593468768139) 569441433162030549) 554433910295547084), 30)], [((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14), ((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn 21567957328698 830448593468768139) 569441433162030549) 554433910295547084), 30), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14), ((pn (pn (pn (pn 360 442301127832514937) 185945552335899932) 357928920281911406) 871856833970831564), 6)], [((pn (pn (pn 21567957328698 830448593468768139) 569441433162030549) 554433910295547084), 30), ((pn (pn (pn (pn 1 759945318841362967) 177312092051016799) 340136674771353764) 288859639392567040), 8)]]
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
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn 149 843930450055885872) 505797776439525454) 556928496919032398) 661851876518113284) 493470220593101046) 193892446344149711) 881634314035232647) 596361870324269058)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn 340 282366841710300967) 557013907638845440), 96)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn 226 854911280625642308) 916404954512140970), 127)]]
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
|0,0=>(pn (pn (pn (pn (pn (pn 31854634496080104 361995418905829154) 481731341722945624) 335329213172062311) 417648502107555733) 166068679035948801) 860594449004888578)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn 338 958311018522360492) 699998064329424640), 120)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn 226 854911280625642308) 916404954512140970), 127)]]
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
|0,0=>(pn (pn 64 52174046900140735) 390958174689296898)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)]]
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
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 14768037923593 973842053757826318) 855795764980415726) 975134075111247071) 6768628793385761) 730525859390393023) 983464195795245227) 255890698867866916) 394949881290617523) 342374097600649165) 59717105474359388) 281075240458915936) 865995231717470970) 815906042930151419) 593365465176135811) 607493535187146216) 543200433323648314) 919321606714036763) 564607449489516416) 33584755482545380) 982367052600843256) 583011132751859308) 56324948311724002) 810713767920017255) 356595720868290383) 500648376068745176) 180427799325612390) 794447485647935818) 506968833937637775) 537884658119558250) 751961989967249408)
|_,_=>0
def stPool : Nat → Nat
|0=>(pn (pn 646240855215 912853795132446516) 477132926891602448)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn 340 282366841710300967) 557013907638845440), 96)], [((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24), ((pn (pn 338 958311018522360492) 699998064329424640), 120)], [((pn (pn 338 958311018522360492) 699998064329424640), 120), ((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn 338 958311018522360492) 699998064329424640), 120)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn 340 282366841710300967) 557013907638845440), 96)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn 338 958311018522360492) 699998064329424640), 120)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn 226 854911280625642308) 916404954512140970), 127)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn 226 854911280625642308) 916404954512140970), 127), ((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)]]
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
    [((pn (pn (pn 73 847128892668893910) 209957812929562574) 56895378427674624), 128, 144)] (by decide +kernel) (by decide +kernel) low_169

theorem low_177 : Lower true dom_177 roots_177 goal_177 5 :=
  lower_slice (d:=dom_177) (dSub:=dom_161) (T:=goal_177) (TSub:=goal_161) (roots:=roots_177) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 287342913979256396 537781937015290126) 747303094857695232), 128, 144)] (by decide +kernel) (by decide +kernel) low_161

theorem low_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_slice (d:=dom_163) (dSub:=dom_161) (T:=goal_163) (TSub:=goal_161) (roots:=roots_163) (rootsSub:=roots_161)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 17538019652054 223421495479554155) 891525103948660748), 128, 130)] (by decide +kernel) (by decide +kernel) low_161

theorem low_147 : Lower true dom_147 roots_147 goal_147 5 :=
  lower_slice (d:=dom_147) (dSub:=dom_146) (T:=goal_147) (TSub:=goal_146) (roots:=roots_147) (rootsSub:=roots_146)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 223010854 808975440799991816) 472557932742574090), 128, 129)] (by decide +kernel) (by decide +kernel) low_146

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
|4,0=>(pn 205101 400500153145683199)
|5,0=>(pn (pn (pn 757131 563073964655863855) 37925495843391053) 871912265369811767)
|6,0=>(pn 587661 732910848441160508)
|7,0=>0x1d437
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61994 819772088327635057) 265523797989842494) 769213207067254282) 489414342239761219) 845154784487733888) 330743326372080101) 941231528092251494) 166924774984297310) 245322904736963605) 706651267753929599) 526415009421754299) 624267825483784072) 796728776384980059) 255534738545130137) 139233922625604209) 916778558214403573) 608466760464861758) 512315422692771385) 271709444052324842) 792823882366601551) 778617952918230068) 766059771108280145) 536510464085522556) 239846261907377077) 459426427374744660) 17241982695066940) 352702303319221648) 587918985912910598) 878520093458379842) 897076716621005899) 380550100561881143) 68801085503256260) 119062143813327131) 137429416500851748) 645297736071161184) 115249439449450301) 747790731432718800) 771694209908950981) 317632339081749250) 130008400884382417) 68173302004804376) 673759277153227502) 660421094489482615) 23309330485408122) 217452530666807214) 107796658256288210) 540407399852205043) 104403228784216180) 951153705678471454) 57579527165568788) 253751568393287193) 414352669364574509) 297953128721817953) 967567208042211036) 362108534512063125) 897275667735459271) 481307951811724670) 37278448772107560) 131008888802317815) 823969500694482921) 807360758083155090) 564927896962890745) 273942040770637134) 145146826205399185) 358189187871274251) 510598364584197798) 694193613436678973) 253355755621469091) 469128800049447695) 363744881344061534) 75605758589329564) 797554172906101262) 338251966212466185) 345384847384973216) 3715271654463290) 266214142377450164) 735216140487505076) 627802851451535360)
|_,_=>0
def stPool : Nat → Nat
|0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn 22362 312337386981974831) 766340475339847818) 437457812044598456) 238874048310855439) 1426864432628208) 256606813482957127) 554758472387326510) 663922018678388390) 118239869425780768)
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>(pn 785029311559669 840334591768867206)
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
|0=>(pn (pn 296021416545724902 12191038160593478) 332548644865790743)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 15438 945231642159389809) 464667825054380435) 997955418741871927) 677867721750618658), 1), ((pn (pn (pn 26959535291011 309494617955681309) 695723670668989160) 619180400863805440), 16)], [((pn (pn (pn (pn 15438 945231642159389809) 464667825054380435) 997955418741871927) 677867721750618658), 1), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 1 177880070162058027) 511898978273727389) 141706055771452909) 953741998239296170), 15)], [((pn (pn (pn (pn 1 177880070162058027) 511898978273727389) 141706055771452909) 953741998239296170), 15), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 15438 945231642159389809) 464667825054380435) 997955418741871927) 677867721750618658), 1)], [((pn (pn (pn (pn 1 177880070162058027) 511898978273727389) 141706055771452909) 953741998239296170), 15), ((pn (pn (pn 21567957328698 830448593468768139) 569441433162030549) 554433910295547084), 30)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)]]
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
    [((pn (pn 4507271050577935 419324338245418064) 121951714805812236), 128, 130)] (by decide +kernel) (by decide +kernel) low_169

theorem low_153 : Lower true dom_153 roots_153 goal_153 5 :=
  lower_slice (d:=dom_153) (dSub:=dom_137) (T:=goal_153) (TSub:=goal_137) (roots:=roots_153) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 17193874548 67110442124038788) 211886721161428992), 128, 144)] (by decide +kernel) (by decide +kernel) low_137

theorem low_139 : Lower true dom_139 roots_139 goal_139 5 :=
  lower_slice (d:=dom_139) (dSub:=dom_137) (T:=goal_139) (TSub:=goal_137) (roots:=roots_139) (rootsSub:=roots_137)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 1049430 819584174221321047) 289319573164133388), 128, 130)] (by decide +kernel) (by decide +kernel) low_137

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
|4,0=>(pn 143272 537595918576269745)
|5,0=>(pn (pn (pn 385131 761239468145212603) 821385573890898147) 332792783329057377)
|6,0=>(pn 836768 634826013136656883)
|7,0=>0xb1315
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 178798334873347 634122163134983667) 170524190790928193) 19196805630626179) 434363230530651236) 178394338111212513) 591519997900115512) 864464016373468170) 924025451012439170) 907955208632153971) 823395790752705796) 884263511238326425) 701191017133057434) 796707761718807317) 673428659858249187) 390625445776751998) 691634995045674684) 757407466325691242) 212538102134745764) 275220085556520214) 796434906397419951) 640934154182977708) 447263027896349505) 234181721680937974) 575635746670076194) 396390953905678063) 278639812556066149) 119187556806135795) 827287056264587812) 311144180562366548) 126090640088642284) 984053108361472396) 118936962487441961) 5008446084653382) 307727921847046169) 907352883135530196) 286457395523819941) 686674821604602041) 369839420683707998) 145028323128575682) 43565927574488543) 126627207359632581) 280326055435297306) 165657205893721321) 782617964268327502) 719703932512340128) 435109969069315858) 834580594148933932) 446567414660387915) 380900299694604220) 969764147409624717) 626030099479201593) 361456023257091081) 565601671821217796) 440202184892210014) 657058818615533384) 37783673784936913) 778657777018721890) 443916886421854019) 582355527141479896) 267006800531441194) 995097419735849363) 13703810813645331) 971566318884954605) 629186437793311919) 942219302484955525) 642361418963704717) 856989738054979328)
|_,_=>0
def stPool : Nat → Nat
|0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn 33421 893814921946399694) 276945118709588630) 145632794246861969) 617621538675347432) 204658649074865258) 385644038443901241) 210395257018979056) 481226291601094408) 995530185319221280)
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>(pn 785029311559669 840334591768867206)
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
|0=>(pn (pn 436732961970931958 281331426787704042) 604653163183722781)
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>(pn 765032 737712109103751682)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 15438 945231642159389809) 464667825054380435) 997955418741871927) 677867721750618658), 1), ((pn (pn (pn (pn 1 759945318841362967) 177312092051016799) 340136674771353764) 288859639392567040), 8)], [((pn (pn (pn (pn 15438 945231642159389809) 464667825054380435) 997955418741871927) 677867721750618658), 1), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn (pn 1 177880070162058027) 511898978273727389) 141706055771452909) 953741998239296170), 15)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 1 177880070162058027) 511898978273727389) 141706055771452909) 953741998239296170), 15), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn (pn 15438 945231642159389809) 464667825054380435) 997955418741871927) 677867721750618658), 1)], [((pn (pn (pn (pn 1 177880070162058027) 511898978273727389) 141706055771452909) 953741998239296170), 15), ((pn (pn (pn (pn 360 442301127832514937) 185945552335899932) 357928920281911406) 871856833970831564), 6)]]
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
    [((pn (pn 1126817762644483 854831084561354516) 30484617281667072), 0, 128)] (by decide +kernel) (by decide +kernel) low_41

theorem low_185_l144 : Lower true dom_185 roots_185 goal_185_l144 6 :=
  lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185_l144) (TSub:=goal_169_l128) (roots:=roots_185) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn (pn 73 847128892668893910) 209957812929562574) 56895378427674624), 0, 16)] (by decide +kernel) (by decide +kernel) low_169_l128

theorem lowZ_185_2_144 : Lower true dzo_185_2 roots_185 gzo_185_2_144 6 :=
  lower_iso (d1:=dom_185) (roots1:=roots_185) (T1:=goal_185_l144) [(dom_185, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_185_l144

theorem low_171_l130 : Lower true dom_171 roots_171 goal_171_l130 6 :=
  lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171_l130) (TSub:=goal_169_l128) (roots:=roots_171) (rootsSub:=roots_169)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [((pn (pn 4507271050577935 419324338245418064) 121951714805812236), 0, 2)] (by decide +kernel) (by decide +kernel) low_169_l128

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
|4,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 5 481114011642331353) 871830274615763807) 878345354946055323) 534086779545462129) 196972117113391409) 182969764193716565) 572190697325744263) 927376429843184591) 444818613518078938) 155908484591792605) 929044130623026296) 151047136255571910) 586360697136299156) 734614211944952198) 789278148351721430) 294068821703492815) 660545706868875076)
|5,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 33736733190937 863312954277989971) 475769138521593166) 510508783855642418) 130224921532393880) 595777652183582382) 723240743431005236) 334209226788613156) 403587209819867006) 311542399452364887) 145356696891689181) 266481298645140986) 516129458882399233) 996612183864424217) 132462335549630636) 585917209751793000) 32889490438311320) 102503512809542406) 957429910056791758) 699354447600239633) 416265749798747646) 306703265900688026) 463916312575059482) 420591312843522338) 39086118830873322) 930347444373363693) 347252122364683611) 251235529215898844) 899724041544577305) 323510588926829553) 40735419624986185) 181648661880380946) 205340132619759953) 872612090869558498) 413582961763914637) 858614802237603948) 778383498361469808) 672780795533732168) 700677284722738508) 296789907158186888) 829293299335546068) 515468017004197138) 29918290692801552)
|5,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 134571723291936 585991625950203081) 222911865041599229) 929820173067311330) 501106294729352110) 436288281102119371) 316562448669037242) 697600178104993993) 683108265997611978) 260932765436272604) 507077806858609268) 779841176206508685) 802993327730430738) 163464057359300564) 896612879381539739) 646632454955241337) 451927543272645529) 740905100834300016) 365324757969124875) 337095438755224064) 126584696708267585) 326000520043055405) 502819354840247718) 509192975956541876) 875945598767821310) 726319541157055808) 630752230332168245) 952713343260593178) 477564148508404079) 235832728858223610) 634923561139514901) 170567988518786358) 500346828591273858) 963702635653126286) 377751688310193489) 451605033237117609) 170669493269296825) 166171273623676193) 27402774248214095) 609757896673706610) 786839703179903559) 174584826249891187) 92397352511684457)
|5,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 6719429761034 719251355560513801) 188461402778848596) 891641620828581159) 644738359629793635) 359226845500887915) 292954612560004533) 376483527508667065) 202662865607415867) 859878066432603938) 367956060043474370) 263088897519428937) 671319943078782405) 405614512568347597)
|6,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 10486478483084 562708766240265411) 596610026124203806) 104871153711288140) 485546441514683803) 539268894917851744) 162283509151605354) 884044436840696158) 237026031835794110) 326332380169815141) 817065079840872880) 556780880972963653) 566969025265201646) 959653596409687718) 617658213897576258) 81241310187466153) 405420630872783595) 821012462028571761) 412152572433224636) 989416462922396121) 461168500945114046) 314576298127911971) 814582728016990670) 461772228165799188) 507604613220916176) 959049778559319862) 953353813299295859) 88798549761953103) 172232428193998129) 205298975363618680) 857305949847957141) 100595302105597195) 128365441207149715) 791714969719515646) 277676439350419010) 682325164299013416) 271221562966997941) 63612571492849901) 273411825139669652) 936965917434488697) 382294613531782414) 786321509673220212) 742312264667758699)
|6,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 28368079178130 702411895855063324) 444557969366860337) 810671272454466854) 641822242414155151) 267463898504590549) 431853051330873818) 831093337393866662) 824149514790110957) 82865465634985305) 497190325443637299) 614651793215131512) 436927756670005603) 915203755747941478) 17817753308295012) 779262331304583741) 701570619367698435) 445559089146295818) 395214070141672639) 402461452777500977) 83261977517824817) 558302468591827143) 912835350345055179) 842269390496122700) 700726255622670309) 307200953496208824) 705529234747972969) 965530973607680944) 399598719837311981) 227528824276260420) 435290679971606111) 300993008498962349) 714932922080051646) 432416186945286396) 268506190410959729) 785491279859478271) 451731093281158616) 789039644999071757) 794211133915116596) 77814218388590205) 411324914803943838) 381881109607123846) 554656308547576658)
|6,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 52525782857361 497316854063229876) 806019912988831073) 469311946313343008) 554519458421734312) 852717581540545470) 443908583777570785) 441737973277281641) 597628279141058836) 762326404727108392) 261064939522027064) 774322065214912058) 877771039819520286) 628132556171855122) 659979404796970935) 553474845631055048) 854295239027566066) 590906310604411546) 587445657530209400) 998486611404838068) 200128674937268374) 840342554052271491) 721684895256056663) 265128072806492197) 504972821641797164) 989731188754006667) 54228754700501551) 280749890543906052) 53329248401764521) 121445670255093760) 899728000688921616) 135865283632221996) 856806252820324106) 118100624759970028) 113193752676513432) 819482692140337448) 525877883792837766) 265667854634833061) 36909640859122481) 894901445874350409) 286259362300733793) 605136177396671855) 64664017855385162)
|6,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 85392672610583 675138599551042555) 197287921667132660) 325528729355786397) 808944177010236070) 685491368943118182) 574251137929135214) 122169453377092040) 115984779088778734) 253364344688034739) 576163166874290640) 582612933070478086) 497239657794073631) 841545431931519500) 715265602048345688) 183787615583220284) 157820927971556490) 780710856961827052) 96158276247159149) 563992503773386296) 704152477498087547) 945554837391832450) 498065262131953943) 640992780481729798) 442266203894423107) 75820813317240789) 753268836477665894) 353970229925836667) 499269912125303905) 496476580109679183) 21961264435352608) 360147112215662984) 761152338844105119) 803788294064456904) 209819549997204424) 263951102378661444) 783772378284559143) 270944842446716641) 589882746784999721) 228247308112596203) 617417584061255081) 325490726848271399) 580868861818434475)
|6,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 191016971300490 306643875151988184) 597219384781385726) 993417467777593846) 354319303584446226) 420043632092691813) 469747178997703403) 252252785371364149) 947590012510249122) 108352183644608329) 88900375017776035) 643408277999501048) 388574741277132330) 408389647734182397) 908551833463830044) 200861687208717438) 718010964890559513) 614820220031963505) 966035102460028662) 607475543664384111) 87710989205736839) 172604880997849801) 616383389985018969) 670974404742417381) 577786778143493995) 993221239521665106) 282519819924727423) 52655247248529415) 570665434542930677) 261798431761412007) 395040740970111076) 107934214554081224) 716386328962290859) 301740988461935628) 746244532886857548) 389283353139427548) 108189577168703601) 511479009616948010) 303804749352763008) 904598717312441584) 245791472149672074) 248947062471643543) 416719679167867975)
|6,5=>(pn (pn (pn (pn (pn (pn (pn (pn 3197797558837 798957842068031481) 548402058658132089) 369583155454068561) 747417460693038270) 335642140629287381) 104866357561033508) 879783483099592756) 362138957526798587)
|7,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 33367308290237 390869593369347901) 413529787712033180) 754753986416079252) 593010081646312985) 619228344007833238) 922426779814217953) 203876403747872662) 588256870296208189) 904730691555509139) 932593166285098287) 965655457875855446) 665726441088505781) 920437832519093033) 36903023901068135) 427582809490008529) 449787032160446494) 595225902784144091) 769567560560080923) 531951107491727655) 809252131940699962) 28109357829299705) 373263100725461350) 119676821457125406) 42244753993259407) 800599973863420572) 471953015912170181) 705918509719370496) 408082664600758627) 825692378080885479) 263069871500473661) 153884394530990447) 293089188680081347) 141646127053728012) 437591196577037275) 667779680502664867) 930577464820606480) 335198953387225414) 102641595018138456) 166015792469167537) 865587265742913181) 537439727521387814) 292522393131810915)
|7,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 103485845351567 399271811458179642) 588517184279447789) 149999639452363753) 461658569794053473) 694354233319633185) 149297256045681591) 457260160285657880) 194086016728084998) 94628422015790442) 446057289704812432) 266092825122095623) 65343788416072246) 432558858353904022) 844062706415324574) 332305199295043255) 974206965945227245) 555457282476445710) 909079998839217605) 300223998514354323) 458915406994138046) 292974896100017188) 733108822104987941) 89289121448890567) 15301884723189407) 838536689706741334) 196870646762950424) 51892479394019045) 587393331053446365) 813195915662032204) 524737382474365493) 722467787021301746) 154698362594364474) 18825741693940087) 783727034774862420) 510901567603692324) 316730401742226424) 776939459846335404) 555177621712603238) 845371663682493796) 425081936483510453) 370832262524633958) 458750014272388674)
|7,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 25123008 137792668342939719) 713999312369254810) 783429369117774907) 952988856217660507) 138748652580682030) 183391023453663854) 347925073194453804) 402358239609696297) 628188490995588142) 643564366524566825) 36135639809627527) 114695815899877620) 541235517257763989) 516589707823534409) 264699030226949644) 153561337728544485) 695635332317568475) 874747707752846797) 893909536665062239) 284124331739233819) 92259878301062792) 986468216836269369) 927734845713001794) 787705501810680900)
|8,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 7876284 51095427373592983) 579556236897030835) 559680553630860250) 109518675802399485) 245178035006016840) 52994233964856229) 335563495629870331) 793676493200683241) 138733570977364850) 437396011071856989) 14966689813426250) 819878346756111915) 207395931114315546) 610313467852200189) 401079741057972336) 603623804079873763) 255823976187826926)
|9,0=>(pn (pn 697070 114946469909792525) 694230733728538148)
|10,0=>0x5e24
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 74682116482 274623934495235064) 156903048024689854) 543091195924307579) 606972812588479911) 447770867247929680) 102602593751727138) 834556302123788003) 335616029052518641) 607343787059617797) 711145747034560727) 914919646102532258) 481556647170282406) 61813217377953419) 146904478926258522) 633758365182222378) 826062115308430222) 540815086847369074) 911169145488635521) 868066837764352620) 839728175244613652) 129135884493683953) 7799072736603746) 358862793626946619) 800656342782580741) 87028935171838443) 331794415938388054) 501463903473176605) 950934304039781463) 532934968019635256) 556945365152167868) 700814663020946633) 737353680806643726) 728814403025180908) 494584028141241042) 745046035746164773) 424643337150804956) 38348597189196667) 635287928094982177) 332494734070361251) 392803957803474869) 630010480826795618) 637481714072161802) 538341906894017174) 423645339553026301) 170327301870156680) 72080663053806822) 483529548334952427) 629829168168812918) 705818372021277007) 373823857135311607) 42155314512711647) 833049801384453001) 627809251144406122) 878844295936994904) 94213739914283182) 761213751658690071) 923479764543734541) 390075220621145097) 493270248598173497) 250613355529247411) 800452902008644708) 508673684823918087) 224618053095796423) 1945586591643253) 869400215298885270) 881966293283653722) 191128931257267187) 619502648472854047) 435896378981230015) 300562306316213249) 479284861202774836) 152729116726692580) 626964146969278728) 822333176317453141) 577619549660438906) 620862617617728066) 430525137656422615) 291800409426744290) 272658892625743007) 792510967256500899) 933393582063602478) 796751539536801833) 558254733226774380) 232291661400538710) 894484591229612816) 454183895062340389) 742591800279726689) 263956135419200975) 177862834763384574) 980797942112704938) 473640024915570072) 258075135913842770) 365900902822695898) 662025487473657165) 481018010667567708) 903300002707927964) 547679890708484573) 700194819973028597) 418034000195057572) 431469001516715786)
|0,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1424421 166050114208015221) 426348792411339733) 712623246875488205) 955221269771919938) 651487521581253322) 745818349210310569) 708146634889772260) 640343254123854628) 295237621862576628) 382574027924102998) 615887482353761758) 71029316823416454) 423260047454349) 565106360813447086) 158404232663041153) 997054738172825823) 692973249199141081) 884617333243115300) 80575969712971553) 939123372778887965) 315685556961941846) 634947178689724412) 469458017503602738) 374556539967000543) 357558900785325910) 494818963053526961) 955535692671606677) 145913330115718653) 716324207499135223) 700218549181418022) 46707266454501394) 121989404722568268) 422328471480802782) 243224178750423014) 969439896321903703) 563685644174806638) 647125667499113202) 457673630158535299) 243743582708137760) 217830056516702132) 144552858560933190) 968845195648193006) 462012110928345616) 503964278875281996) 938937299297791959) 391589123358303548) 771675649472629959) 572450078134264834) 577899398502417986) 351436404357076160) 893996272264563396) 520541182918241333) 245070686409290305) 364526886019198089) 787594683712898746) 951963638953648612) 286500432132324725) 198841366894811008) 68821048269315874) 627265174759713706) 930508049312464754) 139196516378182663) 990549821530370632) 714267736012751009) 222561196958557948) 228884689543043754) 220842316427828009) 992937529050233971) 965566358517840981) 142094312460717349) 797120727884463487) 47849188163729351) 803142204439523067) 157005488683632829) 550174616280680995) 590787068775602962) 204995893825208301) 893958391538866475) 982250497650645403) 239836099242454519) 23402237189044413) 711778968317663040) 97209585606365480) 486491613832148840) 478552265828264287) 27496940914193491) 714777328974188778) 458890043945324950) 380178158158315609) 675943057536979853) 470596214031533963) 905069010236405477) 937794123589005338) 957251013444658645) 622087823232422673) 280737078777188564) 523988456370105797) 378557465082554997) 281061430720427445) 819338404135895810)
|0,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93351150422 493472649400697879) 774768781320969941) 803329905052474625) 274789957650826445) 294470617800812352) 952686444365887786) 402246519372450390) 869455656832972396) 56591431868003452) 39871229802854558) 220052157471332476) 69623639264611111) 629189805810467291) 836883354653740380) 896634529344695167) 277082555699486317) 983603992399306221) 829254822832169153) 303907382617084125) 308861365051387370) 333187267257428104) 406476516981638232) 104166711190859717) 338110091356296873) 484818320171972554) 314666212904306049) 771023543655227974) 292582244108981444) 295228465494728805) 214143533331114641) 684785988346141111) 307032916794441609) 534553579011757675) 659167483554646813) 230477834870129081) 436589937044458731) 976757780880744511) 968437967130240212) 50885879676721306) 725664670673757199) 239304469071935381) 500448967240772626) 812296328961150846) 162055476024319593) 127812849508231915) 929808876495788225) 564488442173018290) 660224374872229575) 356432773919644188) 823142498422165209) 930790111103300950) 555130441136395374) 186313424587554876) 24765215853087527) 788098955633987127) 363948028041458886) 991706138334965288) 252868182239561854) 388353154422227128) 569520138940705810) 404273752925009475) 313550302502926773) 702206757438891846) 585242937440084649) 820532465202212565) 308280754757089154) 174286288248167902) 50536096195032849) 452514874477860817) 413209750358636236) 986083374045147828) 753868238263150100) 552898029272600946) 854316508254742689) 876947463331857798) 758613931752045863) 176201159483442783) 372484602100701851) 249424734475297148) 561989672425025783) 407596119373895903) 475118259591182899) 747125144914604141) 670757282388029040) 409371317243696929) 932252018107448736) 681743242857923195) 685024821466289549) 163238777447506489) 660395504763917150) 514235148760613176) 652315319637427466) 667179506836782076) 936511084818464888) 266911649383586713) 380024880419576464) 959765579198313006) 593724389910711479) 189042708420399717) 910262470701745408)
|0,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 242160835 719868637893119518) 104627711175605928) 454373792948133743) 104646929787505752) 356561679734621444) 481588299938972215) 952301681787016263) 580462833697006205) 895726960410635616) 941611719798701029) 101054745620871887) 11209775668290499) 314198105381932774) 518434229250091739) 767276444330625189) 726044303002204561) 828396759665582702) 378811074737292333) 674434209246199031) 345613185764634739) 645422772904203508) 65794612532301574) 895465945744496017) 393270448488084181) 24320674570872120) 864826303132675894) 25009005430504826) 80113929310381589) 377114725003474066) 164592057454692155) 551730604389127346) 427932315733402935) 915568941052698197) 441564310247413748) 862708631449118071) 991598972767473475) 310323821757467572) 820644126750979191) 697538764540736595) 465161136900883922) 978564124862868397) 978256404472704547) 830803998400910060) 508495154856989092) 628233210007486718) 634216318716821584) 282748506467260185) 413937773246366737) 179310238447742517) 642941744552033664) 341596961827286506) 682111562308987543) 210720405913576404) 341380878571690599) 268901272048902395) 565816864263870429) 456532276559607013) 847575803307886461) 947468387280892292) 997572625566458770) 824688564656865705) 150024166640242045) 925924281937526662) 170297589885100852) 284800140350079544) 482540405311425064) 818816310850382989) 795188495952291016) 392095225454871597) 673089529786412636) 697498692726134877) 780864715786041908) 939662214134128025) 134565416096558774) 613099345163966366) 504638801630773074) 367289112307220678) 780106058907810510) 481386618478942163) 353006359657131476) 719300067130751078) 197478662340676391) 612282935915548754) 159910710609528212) 415885299782987375) 198103139446708999) 244963718737137328) 953090946456421492) 661806918542886958) 487630783358928815) 38360485346490056) 829613455735593423) 661329289621790496) 579783568012104473) 129563461775823125) 284297408713250591) 285296014193274734) 347925984189291857) 395957630604647658) 945801508775526400)
|0,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1 449018250183684457) 992798023992665700) 374939036924203621) 187666858206123247) 24111639511685378) 763209063033248352) 420665254326563326) 374959155467469093) 525585521826936694) 340769204271516141) 682704116723901491) 484830132404646041) 751272462150597750) 704417011030609865) 266589873535363099) 994391800154876583) 51035119493438720) 352668877451963116) 44067770679351050) 942615631826533501) 863128204183429293) 310562676148595926) 282081682311347701) 125988844455156122) 220128904610371454) 571487037679504198) 968754471479889465) 937534128117525182) 584354468686410045) 196487354394602646) 106048767189131770) 361151310587301965) 611608985664804281) 314301084338448424) 583095893659018834) 286852917607637921) 53235949406399997) 791608924826117359) 331392755716125833) 398275682893905767) 406550459991972323) 97798536324999383) 586039166369665059) 472283658369051687) 350898509053187580) 691176200044892330) 705491632275597899) 932162788513709915) 879858089952674971) 580038963653787502) 288002787616481210) 703307659947508148) 838321100020148465) 177580497926414554) 233474581244805948) 41808210653847828) 56577576994151312) 541825870104831603) 233112838232176385) 419472123271369287) 960872488462311400) 101544241801718295) 107966762491482265) 444002522147455053) 123489865885284904) 997269328920896338) 146399590258070337) 166993520906026625) 925685488708293372) 67366985587935638) 882167890141259738) 656223187582655297) 63145406145188216) 345248449159562322) 122713588842190144) 64695568027295410) 443637617528258020) 141580402081224654) 914196804180487511) 447893622651049212) 39739207194409038) 359846546006891779) 423031096343111937) 298346704906241173) 285523887351759515) 807830479295854602) 523893802200887992) 591108285476012764) 827992175884801080) 931857204468310580) 760095308704441301) 350266312007169937) 94940961553954005) 18651518596700005) 545281589729076958) 460473586212861837) 933127463407887113) 516506445832361100) 838499607466602218) 402421973136179200)
|0,5=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93352289959 426334850693566618) 620808261990417505) 749033649207134828) 229833812208140348) 395419642986814787) 818674252304184427) 627812849812641863) 660144863135718201) 833212331013223128) 49074185784726535) 254601202633859962) 631835679913956101) 9670262394474186) 847272325813686676) 555573864010076591) 16164583135830411) 875460167231251825) 262592611280740933) 309276960615789559) 843049899731728977) 45040894297350957) 247773299045621698) 547340730579786530) 695773550003439633) 85179228499079514) 776577530040219909) 436602282460160256) 999450098591032747) 727091525327299933) 243738843835632803) 103731848379892714) 788538484095370363) 943232742005357592) 227111878252428261) 792787040193292908) 204671422218026881) 768790592554659445) 853702101056286742) 551702207408887892) 316041628189217028) 672801484679364214) 855936427108148240) 130886448844796093) 43146366409773255) 114479822154596394) 810837376056693065) 441865592364114290) 921950570745735571) 409087119028067124) 906944138760036883) 389646375669830390) 654919388588911247) 36662419953855276) 668187135450437146) 222966400514675672) 912707927223147202) 180290098694447870) 74416954885501205) 991690630489126616) 954648390173462844) 861786566630640317) 745469448826847212) 761516268123270645) 181198250767126785) 987505541107004112) 804960422269481256) 608537987281607596) 262019821980537485) 804713427603384293) 151107837114296683) 548026233700748640) 157882606210666037) 242180074044574563) 30800967151812185) 757024006857736399) 566478617065764981) 616496066126522564) 628245263240106237) 228768147921682290) 775662262806830001) 558171633328609117) 105128150574002533) 508780831577617447) 777974898488468494) 118265061920180377) 294453475202265490) 412253957932333568) 350304403485806730) 314336526101788155) 332852790637154275) 383211325557826488) 699313742540196058) 341328833886031028) 187692599859809892) 932818705675790600) 782867060688026421) 330976231297734578) 903263446996710383) 773577966399724336) 245641188676206592)
|0,6=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93352289959 426334850693566618) 620808261972128324) 189720090843399631) 370467786177197570) 876674420430835736) 930345928777674185) 599314370463242077) 756348453762573524) 481098440925647371) 339116789021331020) 945254446608656420) 395731255377822535) 37234339828451308) 191171425318531271) 627491586329915732) 815339734632189660) 685114753888900925) 817146853940501393) 124778215033886115) 998637916744898528) 266473705618213285) 288767826132658713) 991330874169395950) 781306227852404947) 837436026562302350) 418764799241085270) 165471183071136600) 715004377623136845) 391793154888337430) 330475984213158209) 248852573100490401) 607696937049340566) 961357965893804777) 518522059336178890) 914040553305727754) 979463637056201154) 574529179755980579) 729454155717141865) 238228480628806363) 575203927012246155) 351055406223071515) 863816481484277357) 425211917247685794) 751919359974051295) 847068172513697425) 599972524381505863) 311722808763480801) 36139104742733411) 687907713984178005) 816046688016356915) 184549338178265787) 895956723186646087) 984820824203867281) 53184502894990490) 636637810290156230) 732151300406435205) 12662233342358143) 556054376063178316) 164727254222126546) 260022106357821698) 722052540731154184) 520142165173421661) 345865391845174973) 18833085037482336) 208987390398797902) 184768305246543686) 8270121486543501) 181299024473019232) 341686231546103050) 351864576181564599) 409917152487358852) 252785850395288460) 134369273546731130) 242194797239980791) 338843225783846697) 149992136885750847) 100356696682182731) 669748344982059622) 956270960565530077) 288127582341762872) 132695063250689085) 755397851162183022) 242000209050215210) 105842044905935641) 617752719266806333) 645155620067279296) 668883061970549799) 71280109560666993) 709747679155884733) 124317312934229442) 364055573348717242) 371085090601104206) 621693117024748629) 377100418977974177) 660873934231246741) 443500714308996609) 892225206930329666) 886895963137954503) 915346129779330455) 606690850525548298)
|0,7=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93351149313 994510828727876298) 130487422131312775) 999389890822266003) 255585165397086924) 484237367801071051) 164350696264828220) 758878070394629784) 384196644152582562) 922948984420434510) 602196403038127256) 852293746595428026) 925406829333558700) 399530978424808346) 674587074402453970) 969432727964479671) 492873052742949503) 298084127697579684) 580627779476958493) 783528636470049965) 803378127465989550) 84702846961729614) 261726957994553464) 684825961892027340) 876417008760189490) 444375087632993866) 280535217826779777) 336653455097837012) 419420673552501623) 737394365239484409) 953421071165136053) 333205424476927546) 111834644639300393) 649380136083343553) 365111224638973394) 201015630201773024) 902479276950371789) 979229964193779521) 295198998170048549) 104965440578240681) 402399908573936641) 133784187046441386) 6746377909429847) 816537130936193858) 183608146424721545) 557041923965525221) 67569071832819577) 13474157674933932) 999060004065746033) 243895635181233185) 984169094912942775) 580946457914152033) 151101807915697411) 139599509733831116) 667799758456292194) 923350801395760597) 913937506558519155) 391918507999049374) 594966662694697661) 796660211778642739) 993812058104207250) 808341654990841635) 191958651033028424) 129136434082482643) 548506532643832875) 964437366180828505) 545703734890007943) 989467389195927877) 701188935532889790) 644319946683323665) 230411228262525256) 859306505077811115) 809947950619001510) 627484914014192150) 867186835450677001) 763318493288985503) 993232789367271020) 252859146435860241) 776313083551636890) 71949773239271759) 877743797194357741) 24014580137779538) 668468330047162093) 849149333057418907) 471011632784165107) 957575352179229894) 570729658438429737) 412718108426167975) 775989017540789988) 864763597250785294) 807497429282545022) 187694919876310302) 561635872471631191) 727992526806107016) 461806246154873115) 66581041561849628) 4279259987290925) 558094842440400246) 970410950325469863) 753819593342852615) 329092740979884032)
|0,8=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 18670268069 63126954910977960) 867315146743238166) 116847761110465801) 154610100599541673) 253849591332614059) 888907060430387091) 884308856581258704) 216002837055801982) 344981056903642899) 366645183837053620) 573476393449318163) 964809526286947761) 485284760407721860) 830306416460283827) 8183818092390405) 502359696947381936) 718610641261538028) 25257240321205408) 575701253810495829) 728466401810356435) 475248708278677184) 37305008666826667) 798792839583160725) 580202161850450196) 342278996812918346) 316289680850489561) 420602487048465862) 492703186706846428) 187113077757396871) 13793464973196182) 972763145574878518) 513388402955621205) 949805833750422498) 18224365114107337) 515532980101579119) 823817370839764912) 877270309987194020) 292464710473299595) 428930595268274659) 117008411391569991) 687444875918535334) 174711949370602349) 561507819138399235) 922668949167289452) 908226895074275042) 155901670800135183) 273093940286455662) 515329484068274285) 659878714247495203) 494537828801681285) 532001220414437640) 139282602921393923) 513634973407701619) 685119456358345635) 910575626582105154) 447484888959509517) 108864952585721602) 614928674324190080) 212087043738149295) 383624524324590919) 700255938089002210) 713275362886340922) 568258206867197744) 456816628982136922) 37612541199353741) 75801399914078403) 537547638759025243) 824908298800364496) 791027275842005520) 940197486888807686) 404230337966177528) 803925377846130893) 406244176856241455) 251585850474818873) 684643249997431807) 290249849337518628) 377825421717842305) 790043790148697927) 5317206025325386) 255795935766152651) 9470059826400093) 998928878158140114) 588742491788570847) 40858452910118246) 259279196913932498) 377468339531659161) 765907591306558814) 619019242911108259) 571249960119588406) 541101054580619432) 584592513489714390) 932499489563534631) 511746062875713603) 977417796508671114) 763151845626202068) 908958534032739242) 334690650112693527) 308021291604618237) 852809723891816354) 253145476138929930)
|0,9=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93352289959 426334850693566618) 620808261807525689) 964192533057418034) 918904723918182492) 398240717822177432) 681771635869223632) 359422660457986821) 542679493700908755) 524685666213316398) 845305479128859703) 773258940857442876) 127739590094866751) 467390689855328001) 417504632542390518) 661214013431689765) 871080010747080016) 589744789883350841) 174394278170791880) 946422676322953751) 395467995971299482) 617308673729638040) 704690966307412766) 269936323397927208) 97032670653488567) 869549973360358230) 733330009244446574) 812748964559809893) 7192620598314831) 35589198818156570) 561153991218238826) 494793378342132676) 820838042421885878) 30603052034351229) 638793003443969767) 948548948173538515) 816242972177570152) 597979958442096100) 833997503629893212) 981335321392093192) 69905653550163359) 145319101343869746) 435524283954270346) 580800663835498900) 215523776346888992) 940930981190480201) 567257912197994312) 750887360911755918) 596830098783330437) 121497394430104658) 485978072228612997) 818298362602097446) 435069132228678645) 377859149132032394) 868679042490114604) 525420849759151227) 925251536376599420) 872114549140808151) 62238541583478994) 61837252156722202) 371242984339599932) 797376024629835826) 26890056105019386) 316808558424810054) 760030650218205174) 353626031545682472) 872346133904479640) 303773213685594038) 104646699577990229) 499870708607049442) 439254890553838248) 248630716963784751) 365764294594260544) 785144056365283644) 435964621179932730) 326368213641777167) 84394020628976718) 749285237597916644) 527570788533334023) 729276981692072897) 283423036564378825) 475971258013781387) 702601664966506709) 498953798827844432) 290184594960290563) 816827672638040228) 766479527440862776) 830032884800807401) 922956115936952544) 888921459723067150) 414687247812251853) 8987867392813246) 137451175115864948) 974414015844801836) 274398200750407170) 420648795591655897) 617057712995087698) 693880032895348647) 770526947080505915) 833413764402826158) 673495582489315850)
|0,10=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93352289937 691392316680936957) 149451598405668895) 325052500464869781) 143880926283032100) 621851847746960919) 21402696887379466) 879287211846449650) 721227397243897849) 357233151228626336) 361052984932806464) 993788106297325531) 656973221665950840) 775414845902335079) 417371252957671270) 437796804447756975) 517860814462658403) 309876034133044726) 185107485024659825) 581735894086220039) 541596914781280678) 774173747337281620) 67883447144100280) 583431477821361551) 942897197765664322) 692892923857055769) 901571821759076888) 337709335652742919) 833867175136769561) 315532916934445570) 981771629914750217) 482705814863042067) 6089225633600633) 101947738371044646) 760467075619376841) 625664963375498217) 333916043555908081) 207004929056379234) 135470737435143988) 387026804959944975) 479444072552326317) 337555789788987295) 760387342838594821) 438594682609498798) 105844620673561771) 601276129332821706) 711274092582379655) 164994171885936850) 86287834973720344) 329228881506039405) 590588358017243025) 176614568768501345) 566570871739180874) 501294505755487953) 495305772816945432) 218732189073110252) 469027748238218237) 549483367035066027) 696892000471928837) 996106379799596010) 677919460389088732) 77560271921877509) 733520705915670984) 10102095182601299) 18373991694517183) 43055020311519047) 464375379317694684) 742681456903575550) 287824880055875882) 386358660007009361) 197229350378959495) 826065647176111590) 944057064375373717) 444515878776018206) 732352824824503993) 385237432626882859) 609162682352742802) 434210206394145210) 466477496335438591) 943070791893273540) 525094167075727109) 716293184361090051) 297383962736950850) 268082133174357231) 655013987706393445) 350714314204417097) 947838583404465099) 799354346458004423) 524447869992821607) 687870749521711766) 116995987724880648) 885823384742839440) 11067518447472041) 136436666678944875) 451709952537660727) 105589504836876050) 100205969408659589) 159886125571583694) 245207040157280236) 244039411904339559) 468198271845535498)
|0,11=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 4 341416547242945652) 351962951262072331) 747833325590120267) 146339481211946395) 756925282614941486) 696228557588924300) 577820170819802992) 684243145099029762) 488322516931106902) 135435210883734688) 531040558001930637) 152073077558416644) 261450133177990496) 891367454708454255) 936285391212691707) 87303228199268641) 34200553386414035) 917849677173617255) 301016754317922485) 749989653339879128) 952936013652327915) 205925837717407047) 575582980566549965) 798977255869575890) 823008109445512533) 873589779179526654) 238242349572957312) 595285362568191257) 198238275338860640) 841448549508066522) 809332515785580783) 788564743557101347) 160580434895974962) 958379341128296626) 998528831024530544) 616720392598038197) 669947394292396414) 77624696113293934) 537399300790138373) 545594306311463917) 494531005213711011) 460110675609451654) 377794829142947788) 42292791028113695) 794661091865720366) 711785150973873725) 151292311895019172) 870797053860965444) 589531727922667026) 27877686230464536) 432808807476813020) 811699993487809467) 244646028881136471) 613036747615120046) 942626945644644655) 394326525405849326) 195847385481521484) 279698126268943508) 382217344186564113) 442563919062018310) 626563852474607330) 341882955892528366) 504976109668705504) 919025657419288377) 164683579302664962) 832873283940314622) 532464447119477738) 145467594218211291) 128483631151625387) 429093232378074501) 678654116692855986) 560263435104491177) 314318207591473600) 12525090089049157) 387354171509574392) 331621636899421231) 861235390177128396) 853277733543272265) 363825729266553842) 393146740723237502) 885377085929697650) 437079883346012313) 613146732919397362) 521098843636416497) 566398638023506916) 175093120829398461) 106305936862040066) 325819611795221083) 848329670092203397) 226750270074591974) 58805878740563596) 302630057816428211) 890338906644085614) 858539666847099528) 811616816181619134) 848275376316440412) 112300320630361521) 64540695180548067) 583059890220962867) 787751813772476416)
|0,12=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93352289959 426334850693566618) 620808261990346341) 639661226239539613) 144807617244339953) 211784215750753829) 474522208061637790) 425809603822324276) 29640061433154668) 976951829481653658) 350255610789522379) 199335764937382917) 874616136107947236) 655717246629170935) 248110615906332268) 799299186916608908) 262264830688385715) 367641869487266727) 133165406159964623) 333263930863475363) 955810196821383193) 761481313166838214) 497092010772704493) 468477820307353507) 887984712353423675) 536850803005914362) 733228587724161468) 65298989557208919) 860097252533885306) 981771038038689415) 107300197445714595) 524405227649494940) 686222170715861540) 315415733449819456) 836736653509251643) 213279041638221421) 793636912859315373) 318860452988929398) 984729897563046080) 989786993981843125) 871977513626200227) 118877212868829019) 465232966139736958) 441277728251985530) 605956285442019347) 947844952093503476) 883497777776311647) 707188976295609635) 113300653696912414) 769568636084675280) 807247836273187567) 280010071939335301) 23025624967887956) 58721794110072359) 483706535715211487) 7549015963361331) 132636880109022302) 646088212280538684) 143331886417956609) 81259315779546893) 377811527341254678) 560226089200883497) 901586210306320774) 3474899610660921) 178804289042484151) 989219636298095830) 123370689583302363) 952801491061536289) 21937814507572595) 34037889748376670) 456559125093268579) 571930669722107020) 562397595489638582) 94360641521610004) 192888998328892754) 831648488828560426) 882532626328507129) 169810035585799243) 798061339283237892) 338419291940039458) 671369694514976645) 205926518071210381) 832266299146688571) 535051567969764865) 320719764382780483) 761141090104712311) 769561056332832061) 555473604811492764) 369848966579498902) 637250578473493836) 503259924775328379) 210926865516999864) 103149225984578860) 108556455092866865) 967739723521236325) 660592423614814042) 628753364448019383) 178173839653621283) 379422015843460000) 310729136032566444) 117909101065800704)
|0,13=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 18670457991 885266970138713323) 724161652398083497) 896479342916044887) 207784453950665158) 269035212673172320) 704737952644149643) 688325606018912681) 680694861309714945) 117683301970378531) 392369269938727797) 386480887885936635) 119134384559864621) 417311077603368326) 409185635151897976) 34227524080382683) 248165997170680463) 424911907013969567) 943836586393886094) 580675217938282387) 166835321781151280) 401942617774487575) 184641930142457456) 22554775126567471) 529388882150983610) 594925178160939794) 75680477822039777) 331164976307870606) 836979482058931971) 971210242272938755) 905585041765192041) 395580617546438683) 345298793774517691) 530545858950223805) 847872943253563319) 17175446650309166) 12005511480524613) 37603877915609205) 247252539118161838) 155721573813436496) 657634849504132033) 931388568813866210) 380395378547937790) 496724345530708018) 61141054594901534) 726154967990032947) 608567569129493134) 723384937555869714) 134725263256270526) 376257679294326112) 386724011856870549) 942766560602687599) 566328330628707767) 107055311639145637) 272371147148522986) 33202947552702232) 938298188725400901) 538150003665266084) 595621055268608423) 372945097412233040) 982236714080851600) 24350642251974649) 359122832922775948) 349921254739929397) 184559625175406092) 363509998210199864) 247096197327430315) 717987183723381725) 411486109772067744) 576877744911545463) 475153199689766042) 933465368807063096) 637547481713488790) 835192473628930768) 978334239930137279) 45486155593780384) 734818284288939742) 256764763044082491) 260922406480163337) 960232028154745010) 618174939115664159) 630797767570836294) 36883394151731314) 103870604507783051) 449009412893623938) 691107248063752641) 779561841146460837) 688150545701961002) 28634715788067956) 768270488897726906) 633393561248918928) 604826562633433421) 395887555648380725) 918981917071934453) 135444790798342808) 348387854067920140) 540707784449082099) 922231468918619256) 942398464894561542) 455982010749874177) 872264455690129152)
|0,14=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93352289959 426004492259351844) 507780575285973434) 269247509796405549) 708423416308082298) 822675591541395955) 73690940107918998) 962322592558619797) 22669251930099614) 237920766763903975) 71881173202996792) 243570598836390342) 994190155801569577) 942403723091668053) 860327941878995210) 456127266446555912) 569978063703296941) 794344340574739720) 183937237112908639) 802809647689824725) 164449607279086821) 689206678296139721) 355809010319024238) 978822018158787379) 731377498188177252) 837490230556752763) 280132073509690236) 936397678953332115) 857621462420634690) 903382569828512178) 247168337966621332) 399731256750024908) 60010931026157429) 258645144746793773) 248333946073245887) 968282320919599846) 1759662461280820) 841731779281444096) 657650425882694688) 256740371842917593) 286554796897890635) 312274319095203369) 651365961275503977) 812820067383199527) 490754666762346157) 959364055466516579) 259282441319828933) 59873008344842925) 731906801612773048) 904972593162883180) 953399561666609557) 670911885039133635) 468501934745699152) 805718060728265705) 946679579205700261) 843935821411306049) 154936040490181995) 740880576886253867) 108279875383263661) 146105387923208881) 468836958953391237) 226761855618442124) 267031384117739325) 302572730782126095) 94760894331241737) 208520781823435037) 72289024328062133) 351641941724763470) 116313749580291378) 61422397018920432) 994746399116506668) 213572682218909851) 780818883913057520) 634337531670856898) 658392931190438844) 393538580634539938) 596455054819062699) 96983888547974061) 827186312743874390) 938486218283986176) 742906249821475186) 563442367471730238) 70050827359145497) 207997553354403746) 22114398821122576) 526694981234240535) 210996288709417016) 952499425101653348) 922232798123117012) 318906944210175108) 662278759985373942) 56237782737710640) 316279200898299555) 607064493367877023) 738894466410835895) 481047055402829365) 105697013008784599) 206327960272774844) 426728740308069038) 984246108375861667) 801626757435359246)
|0,15=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 62355939467 61689297155884317) 236986063456634261) 312131687566762780) 455322853183947368) 424760292871930725) 413730239360258655) 795649365444730467) 482297891205219329) 964942926675871376) 328213618731076669) 296696549820063966) 873678104137772883) 442673544484777001) 71996078303533880) 333582778724633770) 822862385011296788) 206671843508612310) 205222806506642343) 8682306774159505) 878307017101671896) 274444431966743359) 780613729012466860) 254692135433856070) 648743631224025902) 985393359460287193) 379481946872291342) 79050374296792350) 309607930155352518) 844693288150117574) 115342204593179861) 74981693646653429) 875498434469617441) 445861725655116724) 455904693092628924) 428235662413916118) 913004272342577870) 900518387515281783) 34042762779459472) 104403769914667246) 600039469873512185) 51157098481237391) 49372116464657439) 347603891702155557) 719787549230111220) 488866595302325336) 314425557802763679) 62872665597614544) 563624248016874061) 936294706412973835) 285220027309528124) 204604562985742409) 605679008009813129) 134751487474986086) 348697207556084613) 208793047639380602) 146722633287482385) 645175463655026297) 478699941693998179) 673532411410463974) 235304906731593092) 473550147761843754) 793902127824316599) 965951560383176834) 315603239778636592) 871835139279302444) 150417343151625181) 856705397436257224) 616476678696123175) 294446849994275491) 155588834036540437) 189526854553961266) 866552710671303946) 524808030898221145) 509405828546285780) 862418552251322686) 294575504736929068) 515724097601853967) 684187679880867330) 997762743284082302) 223542566310210377) 215589334143175243) 771308798799687081) 480532773222317744) 398179681841124104) 880462320903794208) 633273975476740979) 66339966543979397) 808787794190339606) 303421996542012283) 653461271294478198) 945641882120124306) 625697656190351133) 653836252158426781) 936117646581616786) 364870920874508513) 760201497270828618) 450421634834530252) 30361812150872765) 835525740731273523) 124047537805134346)
|1,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 62234859980 195980721226588818) 557402623156543760) 645188842062379176) 910702703375295023) 522855377375260756) 431754996751270732) 253898314655432737) 660102868471637422) 75756750903824777) 241409055182581633) 666329160349229608) 24145285507323117) 593462536708037407) 605146375601623386) 218971700999257548) 91725823239078169) 734892775137623277) 442329359730360588) 312480364389857583) 865479828198612507) 376457281279420930) 763717601902854735) 91302739305013379) 381606430408199049) 724179155564164108) 765630123097981273) 853835151699974268) 790869937045088917) 696419270714367526) 193045827157827253) 793826473240110937) 418448831138261047) 194700621969904248) 864063866687392923) 977312896068709938) 25122983572457307) 456459112973843174) 353784257648599653) 292711953290598955) 965338348879740291) 106027762124073140) 244751902120738297) 32139503048742470) 173959709382568091) 900881777461188936) 551386329941328185) 9926323423554758) 229250878347431586) 646186101482182846) 583523296031366082) 667010244343917568) 912806731567222732) 874583751977614160) 519070308770414214) 957673775484346378) 809217414944755151) 722506507755865926) 858635620664102724) 773341454994124198) 594236984708514924) 800108037252796454) 388044469060084402) 917222871338322500) 865449349290140554) 99276396613648817) 351252039407370926) 111514316101102965) 251492701686282753) 450047151417100516) 62701803551043985) 384634101763244103) 661659018102943660) 155178973710208667) 698542044294607558) 232412380009212470) 897438382738687790) 962586389845000661) 502551295783377337) 446743017943576703) 375897574809096253) 144339224858146101) 232089148682541681) 713904822705980475) 691938065053164616) 459157987791635815) 775600371576578071) 311726635660203623) 571234335420422543) 83381032742447679) 524733509342957616) 53157137016381860) 674685374101453326) 265381024772658057) 262856108541641204) 4195980469889549) 705527546908807072) 842283653839524464) 855006154477796820) 983945731896314383) 336288428824988940)
|1,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 92987632598 422806199401422399) 471326832840177504) 330947328992461737) 83642558920860037) 491370723563566576) 413241042927030375) 696759637667192843) 845986172095068897) 715281252926569815) 441772246831768565) 644368562401618851) 925726265788247809) 62883340645339906) 309180969595597104) 362189703867291500) 425569712382032648) 839973617698094804) 371787841341514568) 192682791037191895) 893811948940052303) 792686697801582563) 300318992548653962) 385432102079755759) 13718318317972960) 611940457071145208) 42179186955057063) 789260211988332740) 588202030416939850) 761356654108093645) 446492331887240383) 594530344632463242) 533971345890411475) 97918888652206390) 395706252897281422) 934020545745865009) 928943689471221179) 567401684875271130) 884502574900375167) 894571840590864073) 793889960332267806) 821344582265077030) 197986537657250597) 3822096425016444) 974792053738130832) 669727193470305811) 798710637654925758) 795736602116965097) 489033333132598213) 801954781535656877) 672839945704111773) 511951806089431956) 881758245246342659) 82099819277604342) 375263653965286542) 978602319992821892) 663135774034620944) 716400593662067409) 583475701699073699) 669631378614738126) 773138563841685274) 112481350314038705) 889220243535394893) 821753690804354891) 631883018318837688) 612926580419424319) 230824786048724939) 173692955505652316) 749455426853214408) 349210811354666348) 618865067800699315) 421103486847973942) 74942485422237236) 739423003265512826) 927742583493085700) 94054006115283012) 218398264902575344) 512119785517348049) 723442782943617730) 782160219007901090) 666970382699947786) 572338990930583294) 853112178657535065) 242331915009931296) 405846303465101975) 240435410641730430) 339793295312281093) 933411412533129653) 907883580203668888) 137051281464396815) 782260037020429845) 926518686022508499) 991335638983187948) 9391225662387151) 2832470768793839) 118069010614337107) 547300892290061379) 816546099122244287) 143482630301428668) 415136957386932434) 223987748694393600)
|1,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93231212312 813805298506166422) 256094306776955666) 172152927504981831) 169509348250627783) 240686614637108826) 393845370873972751) 129150249517252151) 11936593508009093) 101371794863577051) 348218438001570529) 273268861811252714) 781927269341994006) 391699486793481933) 448772355290968623) 800548745207966356) 306032624080230683) 890854782978230359) 288413976472396217) 81683050249120024) 88943840342542931) 116476015491262005) 127641646774727241) 910519750371130049) 16341046810962314) 470974286041988258) 977129108663802063) 261832890276139138) 373123548248839683) 546811471505401770) 797845180683588592) 496341947904054701) 889634870286120185) 309860293827428306) 159043793537647853) 948095567622196422) 311289754126553633) 188886231446185888) 837619802946714666) 576630521723667845) 169818704885984273) 415611583319830304) 539840112439123014) 586127326629839482) 781227130141601839) 721103177259462060) 614976602883754599) 545778479615916629) 611268575279268930) 354393900129124017) 967249882441745924) 224023658374247252) 14183287864968060) 345536711938134947) 882162388283183799) 672143577081760904) 46064109155961044) 348297933212688018) 451556088731581104) 804482434573822660) 853093783136601263) 783139105388382039) 211658239275667739) 400199232500052563) 762203644541143322) 53825093162840305) 29390104902624056) 390408141239979215) 1178073788559137) 446262161341383767) 240264831929821213) 979142394144729923) 941192830246706739) 344005485947171773) 610144926961001487) 996753362015819097) 725092006753291936) 870888692276573443) 450544400862654714) 556775339165887891) 624827190175247381) 694529154441194434) 172166427588162571) 855663620735369369) 394420387240201601) 590218684264675434) 141663407445602825) 694933027731995893) 666723645546449857) 285142074216283090) 54706518211513428) 525130645698126139) 567999200514136718) 923970391617974350) 274508482903866064) 430432091168830453) 241315459274142884) 275426035955007425) 170164788589330627) 213906650031412356) 587719562032189194)
|1,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 62234859980 190342948072692314) 84764507058123587) 107287843440159676) 69129432789316005) 561919645961960754) 781675358929378717) 221753158071909) 187325822134199731) 401010090015425911) 791219024078506960) 136218450056567876) 353662565169467688) 131365167419109348) 872466584057955751) 537449290153470348) 49881704348634182) 387646390955853376) 316850388099471785) 830257908392339484) 239949640285058518) 295676606619224878) 747284550403855745) 865248252951744264) 42736372619726790) 960025814100437843) 523859846467051399) 205557943091579117) 613213823637201680) 288167103414003349) 697673535189532262) 481418166656471257) 866254414229935379) 783028043697448776) 518325350817820362) 64017672286633685) 607248884924339773) 823724430631630047) 17224706277823290) 204685665385861607) 500746202232600143) 270820119988214061) 343623647093684805) 480757681488322751) 888998707233543496) 261346406896735825) 149087431716511747) 144923089855806972) 730399319289047894) 528210409521332048) 683476761931121980) 484398721452225721) 761009006667651087) 636307873242965235) 144176689141951164) 197870404314021587) 991504707018797400) 628981714456873637) 340634642787742000) 346932215179098670) 499802787830990148) 439833747085084782) 618038154595793962) 153974916878639889) 629183962061897547) 91845825891953411) 630034281939432998) 250200747113931026) 620953194230532252) 621248946270723726) 128327021833415394) 448386433059463308) 5347650922224281) 259331310441500414) 435610126427905690) 629809233362525225) 285850373662392509) 337489842317056927) 58894442059436481) 196947871787071191) 485651791501571423) 476073876414653797) 820005703961324448) 973115014870518217) 8531352620029165) 951933761354508351) 612403029631715105) 107940839157551813) 563962819826495520) 241653142792493069) 542431029083409042) 749462268470625923) 767806795506307196) 515020645836573158) 192519603041677307) 584588903124137214) 802242081783961164) 893061306811576953) 819809195321480225) 261878437102111296) 818345851315031052)
|1,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1420726 169510425195802471) 176215591912218502) 777110940032459256) 316495568447321591) 77932114287648678) 777571825050293015) 23795772942757765) 638027911320564267) 655806533230329133) 196926562352860610) 339865494674747953) 390928917155526608) 467046441896718810) 906163424975821195) 947952055209182285) 642561092260329511) 169492694182067586) 957537992218385418) 897495458857828201) 98882666578173239) 121342294765475632) 546693477260449213) 798750881017167164) 929017744430723127) 24693076683606959) 903329578442827952) 269872623816647722) 717134536171920420) 7181323024718464) 519882739324607699) 732421587898452189) 827533549626979562) 77454527603191848) 915709906367559353) 133630189118681675) 10135247116523603) 821705645499029432) 123762402586377565) 283019669419068260) 976391771029914586) 34450960349370429) 176588046047166415) 177793077908905993) 504019540483599950) 790919483817322952) 774704966389768700) 934444418757337229) 843336031915641283) 916893387254601759) 737035840922605743) 190346398233279191) 235715204334140481) 696529887880952830) 790670298574352312) 125856940108363392) 851893898900852966) 688140883017537244) 313792876460244146) 157620595994490481) 153574605205538509) 519449557730075756) 247250659312537842) 514114420468029567) 616139543276216095) 828387400343206049) 813344674333787038) 415736811633559838) 430367058820203104) 432310248083669496) 874462426415334226) 108685536247678418) 333672160458217211) 327170565022510925) 707284073142097167) 501074539977674458) 646801533522406491) 659758458420899537) 471595927991434023) 274803465687464514) 59641159995934766) 816359746789566367) 778067833799173295) 469642761362654236) 847143444676715087) 592871295701734185) 319589048641369758) 49138791368779959) 719104899990389755) 305417876908447309) 989416224380795103) 492344830683590520) 974431810593286635) 175580867455025278) 229341161148802954) 257234139317442739) 979790543429704970) 821976473670465322) 362318188045978931) 945384107042048463) 893788720911617036)
|1,5=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 93279642255 720402165067148107) 389380929465200218) 870064037854970310) 12148321307665119) 919607059484059535) 848587068980083033) 906577707856800340) 496529765062341467) 87228337451152035) 883041761460959213) 536066070235622725) 899031807753284649) 847650494650985339) 843698249497914868) 636029205945763627) 805885749707971730) 167141947200232451) 125689482762562837) 940172802956100092) 838473652700502976) 888824840850395147) 791174385532266801) 895348048532503539) 123288663075003744) 404742802432979559) 777324885555441195) 656681018925387041) 434128878675980426) 890726591626576462) 644394505976164751) 136969203900004697) 835532918757915630) 606240778527288184) 775006372001471825) 164686733572057382) 632796173342404115) 318778118711934844) 806147812060980324) 436271480107001728) 716442475380749253) 385263534217548017) 868557898233410357) 100240505479829500) 317814941060123965) 707860720346898213) 350295153111327947) 931989755677537387) 447254037957824283) 385303149001511159) 789177487762069150) 441572647625805663) 718826764157343829) 390792073918493503) 423632381966573383) 386596628182255616) 65218637418934331) 88668883340053990) 313905918381668697) 296936290209181793) 536615171636595774) 634430884959469112) 873231624330841653) 852103468338412488) 359862624810513156) 258242111746251810) 485080104780841093) 258750686127485282) 223031856640210657) 453781191720819505) 645141558009084274) 564551638373115735) 461571700068064424) 925960699811050637) 70837384966092666) 580605859896398020) 323350354354659470) 828569241610589879) 906979959248184308) 697815119760991632) 305963767606581311) 518989220203885648) 141368250987880191) 590887061931143477) 186513396792331862) 295297991305529128) 470110792259901817) 995791777791708376) 244439189549059654) 359604842804727722) 288767588736584546) 87349155878511355) 518437596683871690) 810375944050566189) 720756139267088677) 710309260187397694) 305815091780344170) 811176994867729618) 562338824413425743) 316666827110320557) 823479471666040576)
|1,6=>(pn (pn (pn (pn (pn 11198894589851 894725593803005002) 764720810139838100) 71724347335523704) 752443293210893951) 644521150326376970)
|_,_=>0
def stPool : Nat → Nat
|0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41570 164820157600325627) 744237607883014679) 640032126036131001) 855735850297904008) 282769578710776627) 707646808071430465) 303212778328321750) 425001730767999078) 886978577993882396) 954988550729822985) 403971558285884414) 267878414877070204) 206516789485707500) 243066766972164991) 661658200472245470) 396028661006363606) 60691889630989512) 224145044728595876) 476623136785755763) 875840489506376285) 339803351452222464)
|1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1707611 8182341371339252) 390152268830743946) 62084473752043597) 936283958123509076) 887840829951028259) 765997375477562524) 639772130667638850) 797119605530853079) 641969653496616338) 613485528668872263) 43750020544552360) 183377342171492677) 952182854564094201) 86083271063820057) 316115296426179983) 463173747747542739) 964054220255807076) 31088660648472337) 279846630365336452) 893621772558443332) 50176936311263235)
|2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61381 241956724617592262) 528981467066565431) 655884843428957982) 905304225136607652) 494002662657587608) 842445999667365999) 986667226610413484) 707731248020917103) 15604316781637237) 708544142893927146) 451928774841936915) 944450699802015748) 633656063740797958) 777848205551645903) 19709931546238435) 401816866601385772) 256341937215965114) 988049962213983689) 992565412607898520) 550367830372033576) 506282991509584916)
|3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2927350 329933096210647557) 702422316273079071) 986350362773847525) 442144240671049483) 88785162446379610) 430090897415731330) 707391383664679416) 515148009911758616) 813673438959035041) 890910146414016673) 912328849334318960) 141820862753694010) 114808281843644434) 37248317267937860) 612714566361748412) 813958639676948496) 17348425421470339) 282857030652988602) 754444429176259333) 67248980522077911) 992821220184809476)
|4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 183349 101868373523648118) 323004434284604525) 709302093742184091) 904431564581215957) 366914731862892435) 787099745526329000) 145824887949238395) 57763873505355183) 613325124109387132) 491432521225822942) 864263008865575879) 420560927943168711) 480699776368451083) 718472047524909209) 28392352544568857) 756680773691365078) 927923274321992428) 918128196130568736) 927184488759944967) 527919478948657928) 208052132713219084)
|5=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 3821742 396962426127397961) 622565064162876213) 548585835217659176) 802179677835822778) 246714935578909994) 161796810483993543) 911406152571171674) 85547551250369913) 397568349701061726) 16099331323994524) 482772808009282000) 67358883591688372) 353348514969405357) 282163357561817701) 55202555733237305) 230587310852178538) 812839468024982552) 321594500815282597) 499479957316039124) 850601284875227824) 997985227552852996)
|6=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81351 906925611242493408) 526425811184221572) 440944824523422210) 790926630234226903) 122005543811419324) 344776582570850721) 334635064952837136) 507053193297346343) 895914931983487187) 336489453633120224) 716044318355698676) 210935758214350151) 874778047978564916) 739630542085394828) 634129879502243911) 60802699061887051) 171290822821911599) 702074913085861338) 631836897827550115) 965016486208848498) 108512858465657859)
|7=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 4594185 952891087381192772) 241493713582960859) 690752361002963004) 562766491933897036) 918870443080301726) 365511193704152086) 425570939544936060) 182803750584879041) 75411772511553781) 919407190600453011) 9139726044570025) 280095700156816339) 30013254035135775) 219333433888321556) 135173853078528629) 81076174067496389) 560247360156685930) 713001219673280447) 944615688965316940) 295621090605352442) 502436396451704835)
|8=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81490 867168508089037424) 547609937075226520) 806496242323975976) 259900085998020062) 451683662170451664) 571120167536743240) 596977737350184958) 808983562145527177) 583059674011904764) 330790968522783670) 937628921576638950) 394760209758392050) 155272234499458649) 102259870787881022) 843625779102247107) 999932487119033442) 919079369652441735) 318067404431964698) 736842187513590841) 911026428316295302) 549745887737809940)
|9=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 5265009 862715199729100644) 510669996414683070) 980190827107981362) 306892808517208640) 472501755549293668) 477000780874045804) 687612422143526795) 385516246541343852) 770106126833592958) 499288905123188617) 345201652117300033) 825385442326188979) 251161540910590327) 458992048370835880) 594936512623958775) 158650872653130498) 465993108190683235) 924423828227395915) 638698501789184820) 247839813461364555) 451366277481830403)
|10=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 247727 621304619201953267) 803548121899178373) 486984916739343435) 771199769526356718) 969377476599968327) 643976131897001697) 197717624706826837) 302181105082529427) 423806555379260151) 507362568200518131) 21615561267942156) 7856330644883212) 224104848047213408) 239373874388647445) 776378031122446914) 242092709311071463) 450341874415140655) 976499953390558476) 247700909576022974) 606265866590075364) 30595966844293147)
|11=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61063 775909565497129153) 776105535037725570) 566299953810912365) 568522078974612535) 190502855874232820) 790559569923574275) 289950322839623067) 3728552279132534) 268148183823049561) 921063092523821480) 77982405962603894) 549333446567826731) 712396671002700180) 330317189491237879) 240618821754344452) 310957451999587531) 104206645300476490) 223393443230468656) 814067337186512426) 80951059723652768) 886045871910686726)
|12=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 87426 307673742041926238) 615908435188273830) 249166894361723447) 589724215472005754) 496463007400507782) 859296573257347011) 426798780042200743) 900873902806398981) 762634068609883367) 521125698440136997) 179989560376058627) 655419004260017572) 556311778929158722) 742183052671742479) 644741640450476597) 142600674313750634) 996601532609381765) 29352865071564597) 34087976689655626) 108471624748184798) 138261575184823370)
|13=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81431 470495483485392385) 555228778043744038) 263367449891471771) 656762325523455471) 450004472332397922) 234129372512792717) 545692133743440831) 421559235443664645) 714670198417624180) 397738527021064043) 613347265419666359) 102861943232085052) 992672419941062655) 803821431963719289) 343470312705580912) 910021439072099030) 520310820883230763) 85389954169063352) 873260676826393571) 694763786156193811) 28194148336299014)
|14=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1057115 246223975053831340) 680134337680918630) 894187135151330990) 393413032544604808) 986141684174755224) 927444726689530096) 922521543242192527) 271301044340103899) 906052931227716497) 957928899464031052) 271997968472852490) 573761591613138405) 344257894306594272) 279788168278257755) 515848371770518645) 444677652543452434) 966645313158101997) 92837509235610781) 291709618379587625) 606760980742553555) 841724105181111299)
|15=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61063 500469468046255439) 564574989825690474) 592024020298532867) 894635757093428914) 550727917835683421) 839890351310355813) 451620604144897386) 360012186775253918) 772693100761019691) 140968637589103403) 383304403657968338) 968827836155089515) 838169396662380479) 563361855913404022) 166690112544205410) 969172237626865042) 474564805190187256) 126775697107833450) 931952014792410742) 42128051929386469) 415592211869887581)
|16=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122365 45187640110211343) 198296841001719667) 301152051508607676) 324800757422468977) 161179107713150920) 639476028629217088) 382623583101577381) 688569103216151211) 271744549944488811) 268364155454846661) 117219299816531967) 795715062542814327) 846288863262712682) 103881290319138479) 404908334524662979) 518424364758176940) 553806857871806556) 384204039178385115) 442727845925707805) 298513627434027144) 404965752062349651)
|17=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61063 907391733525665718) 915582169538795802) 870094955864527007) 567662036137182039) 71908108692767951) 474348183265785259) 4895528855566132) 520483247709834283) 903162092742029285) 18434632990166364) 359073792142298760) 839693075530482975) 827274172482289844) 927742219523710788) 440720028239530586) 269578373137742079) 957263201762510489) 502094260635142464) 996551619775072325) 79250980237802923) 183089673155129348)
|18=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122206 697884580322177838) 903914425611674468) 447371199049578903) 148525862218204053) 206301642894263012) 141447631896373729) 411428005467790744) 146037559739234467) 966990380516786753) 135454916571436393) 539444721099829242) 746806356537908780) 529441886071686367) 393764017856132351) 773751755794476008) 831846053110036449) 78384058648055877) 501988570694745956) 989391992590631758) 243688418343761705) 849313721578434933)
|19=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1707611 8276666898150285) 414962375503378523) 818091724327040729) 883711772808838118) 359238723485961396) 488966593154696449) 841316492772974928) 386727678047231652) 717978496164154505) 512316852893967134) 227917657108076300) 497861237459937127) 649609230132570322) 629254414000822442) 669992694921123393) 221568465535297138) 569508090492006245) 220213130388532279) 712960241869512867) 865531930247227929) 203800204443127811)
|20=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 406679 193385318442225090) 245924154245617877) 612881779604882766) 689527451002422482) 508267530360724012) 705725153751499253) 985515362295611724) 864787037757172033) 621841911928764136) 68787781448442033) 317227010800560278) 572269795940015947) 927038498528272976) 431192023591608109) 130300164092132221) 70155856050562633) 38255383173123818) 940890825719423881) 546058029611526838) 909263869471631718) 954070356916235284)
|21=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 252293 531944158289517590) 997396418571656422) 743004148799796217) 189160551211692245) 985728711408447649) 934702383585173344) 350875615673362770) 314294655826919579) 19502748063250177) 418053639531002374) 939071049048180511) 760610184560039906) 668783720381820668) 148527189001659363) 500019678008590594) 444148315101603949) 678110934760719622) 567176324259055034) 197004294883696274) 774017538774897389) 897869270218444827)
|22=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1179559 646725854228864104) 815352666338341013) 913632533530945076) 170769405197463483) 570466500441519761) 497231480285794078) 102729541269081206) 219876837912531482) 574061831066095632) 606131678104911475) 426362822596888567) 669667754917612947) 422607593383407166) 219274631520719936) 216825012077680732) 203614841671930641) 592060098247595933) 513493892297328833) 984825365885293220) 533883116234681996) 746559401574296758)
|23=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1181465 368759737633031831) 156406654277390525) 827144880917732806) 764510558954443362) 750440138879544900) 763231231473452986) 49548965712926093) 577829976241107800) 562724867262700539) 408301095624265384) 748860034489592008) 581556980384280837) 977191610850875372) 957458227781808392) 865449902054789658) 849743907399247318) 258919367637878161) 757253434232280717) 833691647862878429) 866320476395391879) 97096308641509379)
|24=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122505 91245737788933501) 874844516358506327) 982259310789372854) 404584227751999726) 453741719655418326) 631341759172676479) 370411186199826171) 197125814999059490) 331460567113666498) 769027462239532052) 987631648318736376) 187235436543554648) 198070879953732215) 603229674557243910) 89376090094634382) 266099324435973250) 533383390095596092) 185979341092546762) 925805294995880102) 977748410598451072) 695571139321162764)
|25=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 90602 730835664250060297) 727219415707253438) 727008221246263582) 267784827831362387) 885232504541536781) 567112895417152674) 30298255480784368) 978585850251281798) 388901118194080495) 303493863720161232) 547284644503734705) 831776702782489306) 269688912470288857) 698739817308886934) 909761832960940005) 643970383269556005) 955733736392157934) 928846716940656927) 41296028650091675) 242018085769196495) 400873770842345476)
|26=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 406619 929733572799233660) 362708041413865153) 186144320194535615) 863979071355788578) 141563401793882099) 878547601656456359) 507002523174532591) 505043542224579959) 432582456675138090) 255285798050893301) 194472478166791766) 632475674109604951) 803687268219364448) 257978646495728716) 9196665538542179) 739349098409905061) 280982172683405545) 981095466110394777) 288466182793523384) 759928521637354257) 229970005252118540)
|27=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 183349 797900186346515014) 588401185183023729) 721929606063141608) 579319758101996524) 528682390663133845) 810892475366935000) 959264670204841219) 165335655184670827) 275809389907732946) 673498681342715438) 226634959475500215) 792953983398367336) 391390499950066547) 489925878483749077) 268585972863450207) 235276048268287739) 443657632809062913) 423362904325738054) 758275797714117643) 147211751740764445) 347346880030331356)
|28=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1179103 35427059242561013) 106642946735074720) 872909252856540149) 492935932645142453) 121381575993291907) 652373912830772865) 219259781188478338) 882917252098048731) 721698971098243838) 769600046640148975) 392819012888199108) 7059457318918901) 680675995054013235) 603841653228732369) 180614183227186497) 602404266808089108) 822426898384338196) 482108934427590939) 956461528654220963) 495605102817089235) 520560492117495867)
|29=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 40775 332043558422761165) 878825779234646244) 598186591060401364) 183165897316425366) 399264333386110486) 321400704151295635) 94494933822031053) 570211983225050452) 388234607056832654) 661063699339402861) 531223809566937262) 330295587976454478) 225133255227560584) 326916114849500301) 724461859256320343) 770973993266041742) 126311534992461376) 681957789723904554) 556106291948056318) 974197585795947236) 64786651817208834)
|30=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 5447961 640469323612644399) 768598590379992996) 892780033392417861) 572988111591684342) 82058756888388787) 756957153870907579) 362820604270042453) 376147101991816403) 771998232254120096) 657743380247769465) 788335427265807519) 780129859743278192) 642700829926144372) 746559065223848136) 613392238285154733) 486781572194506245) 110368581981076302) 941616503443381672) 823257761491912175) 569712824508647766) 801194510202179620)
|31=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81849 107075821815698194) 577454384700041697) 606312880406655923) 560508248654730759) 950101690051565005) 272281900927045427) 62812729086414118) 943897052448935365) 938831300773979338) 145122023890860655) 368804611793204842) 522787824993639374) 735735951788667371) 700533419073979221) 487637951389011288) 114022528565525578) 759356937071793634) 565182824095199686) 504408933574072053) 200919240626014564) 808639326411829274)
|32=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 87068 998893010711876924) 531705512098082288) 973816605010708544) 34232459858565283) 18572604579938133) 135868193338036290) 289213472686065028) 575653916501201580) 952318102418264340) 646684792405740275) 935749524055804020) 81021916988544045) 809605422850231389) 155299679006755600) 697585787029638129) 324956700253078439) 985149261553391148) 749315678245553807) 572552453545505361) 388624992728361262) 46999902975178755)
|33=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81848 350044942102137966) 900549989194094976) 397972113779458257) 33508438218339647) 189654468887725604) 637483386161253879) 768927042472443036) 657763141717464817) 950929247350110503) 870046822491424610) 137351438891554500) 575039814562235411) 651047399229393502) 952990242933389901) 681312158821033829) 471251260454735666) 106900223926061152) 735791824204581920) 307567072252076389) 904096677703162718) 454364254144358427)
|34=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 244337 775368625317828447) 315165717317937760) 103526457102149934) 733556874097442779) 280406044315647488) 948861930227243864) 42222568674470290) 400716995121033130) 240107724661656109) 639537661572236721) 777490556662550033) 270497689765913038) 648457452607501400) 41571218021947869) 310586658625877154) 727403155100185820) 769297655093380939) 816923973004915715) 29226866537788024) 157995531835449089) 200722437175778510)
|35=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1504331 82334766146303879) 743277399915083469) 591927448252233033) 982940137873188783) 205750785028651318) 302618712127949032) 797786630875567404) 932215010657502996) 158281814806499046) 909579338594357028) 463515443736398303) 711256122843447983) 682057414471369406) 326332546363319466) 770343256008366135) 505460376590023859) 512014935545384377) 891260149677750764) 187636457764435378) 600887908955162036) 856935582987717638)
|36=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61114 176046119184986072) 942422359289764623) 353587332468498834) 753904277994410883) 7137541465027264) 890895408394180769) 344686910984611945) 326113980141877605) 209104655145930536) 887596418635244245) 113156830772381666) 616253628368933929) 248293137799966554) 883626199980403924) 910083082635025729) 689491242349154700) 786652987276190410) 735344533414037168) 491563421004960969) 912221904874650484) 345663561909988633)
|37=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 4553530 277784770922052230) 111530143811688927) 65781921975859190) 76797271339767984) 985220591475768825) 95668388800521268) 46022870247979488) 416776283940963022) 636487571643175122) 592764300333189474) 681466418977120647) 150938473797381835) 799753435886342587) 115216252660329322) 863441530831918169) 869916176080281854) 401861312819465603) 845135038131536590) 520994638784866288) 493395857303507047) 116486988055719963)
|38=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 407097 840875224018003241) 958460254947618991) 994726924503896421) 812896721332303272) 590437717688967407) 42035562573586852) 266592571534848305) 796294114295148631) 995226027414593759) 433853164359754050) 818369432809088061) 848563252439994520) 751480415488411915) 770685621515575287) 756067105087496992) 253127803355867900) 543018726627405155) 302171488372829289) 297559707708023928) 890492748116586822) 597143786193694747)
|39=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61063 888478748312141127) 370363855595587360) 689535925054710691) 97975100321139720) 870625968427301958) 651989785320832125) 621642821349076967) 799620912433872178) 198203587305017780) 389197295540469085) 406229610928605076) 233917806002250960) 190124348889213203) 936321050117295920) 458400107515922646) 407845956904809640) 666127827146438125) 114440377521743105) 147038955694906411) 766851755336371137) 523958286735379460)
|40=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122206 697877510156164484) 202295896554021469) 23998016989959454) 790450275634908359) 727448147579925070) 566483486503459298) 863202540317927260) 554294507775311645) 2663213933013518) 563268351122736670) 854148372772406587) 437588573337591247) 688543890479225388) 382570739137520422) 366195325896510433) 491534788449313472) 521704885505152840) 87491801358751235) 608928662955930922) 81902292492491671) 473601768406929410)
|41=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 305317 37055364023934599) 637158572305845234) 881740754216971199) 901464023838952007) 209213382708253686) 73730945429691470) 452042331504618481) 437777380811131253) 569760460992099734) 774100828758585123) 469716348084820838) 548597692462825270) 194768897847886660) 820937134393423961) 130475576752788893) 257266200429877053) 607685588860703736) 691273720165307359) 182015811558838722) 836955677793704331) 462361988344077316)
|42=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81551 332894925760701410) 489037474099004229) 991408873357168962) 319041750268297002) 422990504376085888) 652272285053477014) 896253913009943301) 603297050426429848) 594796976661827922) 886045739431510710) 841650510673161245) 209863293531216778) 930351108986345300) 301083253013458139) 787333225886484405) 293310749614340303) 741816269188867571) 273985372651763061) 507584020138564506) 128021934137525246) 574809682049814555)
|43=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 73312 181271938313198144) 941210677551674871) 165793363089573771) 961053365820995083) 230773413129815362) 685269200959122438) 699250857734639476) 763481109084061330) 608183021171607271) 596070005872627192) 319039005679752292) 702139447591432108) 275191469509542482) 113444433733065843) 475285194859486404) 21809702235005420) 17207817023418042) 230088054156331103) 956224705095037575) 331155602502079274) 288707865492551683)
|44=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 427007 11488313959744289) 333051980946780863) 945740784778383495) 396315715494233679) 889636810588241967) 454488315429678008) 270853866682314704) 785097931990303237) 22524834876208176) 781741797318290591) 814008537152212377) 554591129477643408) 123289554436636023) 982403984693911770) 695939316765313223) 206497398737627980) 495705758591900707) 52981351808486349) 663327887624488046) 101605694454744050) 249684256248829964)
|45=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122206 709596375592312369) 261504067989465792) 575469114797508799) 17979666939644917) 817721361108955935) 276589072688083860) 806420431360017123) 786405603672103356) 298740506268330981) 782095913785052612) 656590323264190595) 899901420473809613) 147811235999494365) 247093477440988401) 54110238123369686) 223178168905917307) 831611917681963248) 926867265217490644) 707863891472626428) 964829290706756324) 34404833012229132)
|46=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122218 697665728813530672) 987587525099476699) 288221266840860930) 49752709861218882) 378762455627790734) 158446474205715322) 726820395903065115) 969938508692332575) 608830473747383183) 790243151145404678) 788801765032921843) 967496239450411650) 739537778643399865) 820212732177809754) 284579394092215719) 946364150973799254) 412851755156796312) 845516976118489544) 291644103149242563) 343087748346244158) 408065956363374612)
|47=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 243995 582175581602555915) 115451513993282410) 435153840736756089) 405180323230146752) 103546243557975052) 980639324250325723) 918515543687357162) 857417387288099843) 772185662370287333) 807874103584435064) 412453544353799303) 33053780075977162) 78031205609908451) 628626300380707460) 759860851662011055) 199710057555583952) 343700113698961557) 632720653600427140) 408609442382364966) 949153277961439059) 669257222974623771)
|48=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 548895 618987982349439670) 854204507154486589) 735410586209924626) 736082716611456992) 483348319855207202) 823360823407215304) 634797240171535626) 588902608047740186) 475485652899603561) 112669731019718462) 303772568398515817) 677383126782990522) 915357168657492938) 938237709021110147) 509520148863802185) 175857588258652849) 961564640541985774) 914139873074318744) 541915678093797756) 503874184708180863) 903632738697097242)
|49=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 413269 735260920103095668) 2893299701138108) 219210452277433502) 791608405215066851) 24535446149591927) 401151097535177746) 426568934703771043) 618644363999739134) 177763837886881371) 860384251192572721) 699301835135625936) 307145234065037517) 144804291880766018) 672731293809098142) 385348360054453810) 949139900732016016) 386378543623300298) 281684615064794568) 570354048448326885) 639920383225685959) 745602451299896324)
|50=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 244471 980740030360031579) 310429243216094892) 360389893322575633) 226998050412387635) 37780443577951252) 299695646717069314) 92343180024260649) 834633912417219222) 779533601536618508) 392789148561152503) 76621424829158133) 312932734511203194) 644741439268397111) 48403237770196700) 187136588117883892) 53828423095957867) 116837953141212261) 627177828211694479) 485427793945121398) 123912760471179309) 193227174143864859)
|51=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 548977 179202513264040846) 654988400850074544) 959102280918280643) 496416735493619895) 199760655590194955) 679877057456730677) 779749058461117646) 990034150491207085) 180376553257424543) 501204024527608389) 797427169887490519) 180282256997701623) 581025714827236098) 154959919556269126) 122761899218877632) 705906704121857116) 890327109734581882) 286231154605728551) 44370835746427415) 49824058258410905) 193564208520760326)
|52=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 548895 618832422784477329) 394594844819614532) 667160570579551512) 832848746026644766) 863161588495243268) 460866859115987357) 598219716419693528) 872625996041945325) 936837754001566573) 578515437979256633) 663596811935779647) 363858708594339799) 869006410371746707) 192035036439836606) 507075427883627135) 660311693771246545) 598640645770869851) 985659604477475396) 56892324897995592) 763915209389354482) 87684686242394138)
|53=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 409398 856464866043032123) 745701887111895975) 880874712717040565) 58553366618590716) 463299383591970331) 193729359245297284) 195954553964452467) 940028976226262267) 435330462790482237) 111819822378596183) 168204926727269282) 864544557873709409) 442534417145730912) 960034377866073536) 157046082892285245) 297811889477822340) 448351446722406643) 696488094606948708) 951713060644546484) 224130296773301489) 330141866850529419)
|54=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61063 501339874532087604) 604970834190073552) 562993443133761761) 238347562766649396) 114615576675351286) 38251234855282182) 989518202860178617) 30664025136706084) 857537065321526010) 121974804274437585) 539229745936248040) 246446900562267588) 56392151515713979) 371296459347068533) 67012978447603493) 647816926698468546) 546918532143894912) 275023291545085266) 268969337983818031) 470462981253008044) 88378368312013839)
|55=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 7745501 276775182432910519) 618962588245218019) 659091277547346739) 70827433352633474) 143420765732378799) 862522691762481339) 531737268755496707) 58080540621427363) 269011098621764205) 306607005050415239) 729032342573408187) 775791195048867250) 721405132607784966) 489466291250629313) 89177463491201036) 182446843642380907) 740196653048135070) 785778731974494835) 344406355511557900) 204393087662277535) 441771612419919178)
|56=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 406798 574571593052361845) 72794665928685703) 137745515546043484) 343250261858741142) 509928014855723464) 907451519179619256) 264896320085100129) 999740247360118066) 706791891707771044) 512992648173756312) 3695238002734995) 540910031343396598) 647512662247284827) 732833226156798156) 871260665273456627) 798396971782135461) 123933565899879620) 167240839358768637) 473777651717054481) 604863134264253394) 92279463554330628)
|57=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 562414 528255639529258221) 890455738120843868) 393388797767825972) 576217139647197325) 548021649344767497) 792059875805295368) 538809673447529050) 598003781367433744) 236188764732631360) 185714408352123079) 456613383243002849) 681845631529243145) 270422774266432174) 98996338748083195) 513488489553181628) 440350780179487831) 666750714231082859) 227320055961739078) 957430091088874803) 412407304388226161) 218863456532327481)
|58=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 81434 588898606986106560) 840516018489547374) 625673817014302983) 721084094814885390) 278951384557239705) 295945422002369634) 222010676161594660) 535833635291166675) 842337526497846270) 202250768616034535) 440414191285103564) 583305225552196142) 72784547263930712) 766799734916788714) 604705905129278611) 477909846986409964) 427800689606183492) 376314298969868881) 73877351624772736) 233924730371019822) 121027444748061708)
|59=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 407095 902905648161877878) 857760555146974646) 750240213593265617) 848230700427864564) 875577195430181658) 33042253248952303) 388170767354578611) 895351307757789494) 726949167095266820) 681820036492589029) 166321903831419561) 440179655815012416) 70303490687324820) 676430259584860860) 401844138658005556) 202455977408784234) 947020790498662651) 373984863588321270) 752860320719485270) 59585120084844594) 532062819841541147)
|60=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 406800 764824272694086712) 685196495599348620) 826052050052840755) 361316080330597133) 878168021572959268) 617585034863588132) 303156199832227136) 246015653786658179) 410640794229870288) 174230325345743899) 219496004346228634) 645338449764254841) 378013084302749473) 175743594392417561) 22246991834532839) 175477830712132950) 622849631606564184) 321886337375651707) 778413594141062324) 789179939282502422) 286996541440790534)
|61=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 122047 595966976207440945) 823087082701950802) 581448099572296149) 288111038651756644) 234973601106476057) 327218519124892893) 441979935143255230) 67624337428798996) 787862686371154989) 553039332103750827) 47345743697481586) 193919662535494142) 545499658282176135) 752115617366814083) 477318387674540155) 8093949323364201) 241667766887702522) 597265396073072206) 298511243569412401) 849608637776823241) 927399929413635076)
|62=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 3618621 399814462656345136) 612799726730524444) 347708738259494685) 344285597412158910) 173858819043187811) 440444771464152440) 857181340261605269) 765704015712713635) 559660878647005053) 700294086408562732) 850817598951419769) 471354693343023676) 766953328433155119) 186158579919944917) 505548408186447716) 248459620630545150) 662856712639760170) 88961258865014436) 337831846357153942) 705130020895382995) 725336973740625928)
|63=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 243995 588441037930910064) 234896957872998370) 233766150590257338) 334599688566767287) 917693378135751972) 128869875014340884) 11068069164629039) 151922070081184866) 839635311583496410) 366305667438307884) 390582314124528243) 679930547363764931) 527452983130674855) 728633119991743552) 849044369392621434) 624083815191815492) 902472415988026384) 850114053729868257) 675607276191802313) 928528149183378892) 938465702922164251)
|64=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 305158 184837560780187120) 416402253293205343) 160274923041500570) 108999803477511921) 106937596897990444) 256735588194502095) 436425446037995078) 707342986830252344) 133594761997031112) 893167842119435540) 587464155152970515) 787705766987150569) 161105512313950574) 355038041906593867) 627106534019277309) 146269234249383131) 858050261486292330) 140526194144560188) 385262761394301261) 305401575051039089) 978873026127597588)
|65=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 4534393 48812902357162632) 795251087606817014) 999939591343944204) 496698260816561380) 172308345592555306) 385148268852660619) 899840041632176500) 758863868400700388) 851718456794410535) 81318962633073440) 623114016901808261) 308896883169078985) 522167997240756649) 287592519111913078) 411704105199800991) 688806318592551952) 622330068006317755) 295792752037765434) 341539583549526301) 329504539958417947) 795941730573125644)
|66=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61103 474988839653961046) 330459913673814104) 930963190055049967) 649279177231905692) 665339666213295029) 116612226391983101) 209771493303478264) 572530362358997793) 951263552885541763) 312713977995300402) 181932336067794863) 383343932193785919) 807496865527863811) 612231804654260558) 627069282404988486) 519628489893192910) 338640551665693699) 739970886450332571) 873337306341214285) 259430189319449582) 349262154924833796)
|67=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 61063 772161096032992154) 699855638499801879) 212986772126262848) 355455422943398369) 485214247995378087) 728308750271082026) 745903358197862898) 952968580412189629) 331663905270695415) 680233345630068318) 694674754506742022) 511421781340723698) 554167827348880296) 533676195699000721) 268207579126800594) 984032523464407151) 522032644605256511) 855419682106654630) 115495130900095323) 435481440116684943) 321505314170235908)
|68=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 406639 374120435720951519) 268775273303184722) 20713463739638445) 157942315342597801) 503535351539384982) 326845605403816827) 434486973183142228) 85425708701967558) 670196659216866081) 422929645599607354) 692411425119828690) 629203075149203542) 88673457417773842) 374083531607098167) 856617337416167398) 362905984415926560) 424931718489907364) 251500804314564279) 131189364947156985) 958136941339974632) 691683728798265511)
|69=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 6728684 707476523904305931) 632222409035284165) 6746952906569503) 265350712595604802) 979874178479871587) 325978273630122470) 936218424021419019) 535409074644373469) 489449446418518845) 792449222354938489) 708791943687748385) 361749234320464971) 324764791730876963) 850726670964464610) 221670782793965503) 259127266079992472) 204264586412900822) 511584065480833508) 101733664815681884) 626624474841112663) 127340556013818560)
|70=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 40715 617460084897854767) 572492929645447267) 687569889764929707) 603206297036028881) 149574891400220636) 440353105784219891) 790926598058796394) 711086473112333038) 829735218890362176) 455623400344766018) 982132159892559842) 397436858240436491) 669161651853787412) 503532393322702090) 595191831707765335) 503855274738995513) 718191780499962817) 476204005229919729) 940428924428513505) 89341781911668795) 696190732316463108)
|71=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1525135 667280576045385192) 676849746188606980) 369362634936571055) 521416937718477014) 504118449123062973) 123960054684532685) 439253678160102716) 471222930481464765) 137245546577563455) 728802703682161983) 934201088880470363) 88983809918792222) 791940914892135611) 303423872444127221) 435117715292022359) 904585592843914802) 947262376550363537) 487669590134925881) 808439233863444922) 237278797454468568) 634876015483747348)
|72=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 125561 474858359546641703) 68826540005494775) 604249816359609237) 554739513849723429) 397395862701063235) 482991006917659121) 637359841582135476) 190903493804576518) 62998331356354073) 876868876105596594) 792197972322457939) 500563942375988362) 888199102162755720) 315110120797338282) 713922287735677900) 598859685017856458) 742995204465734502) 317036716256187123) 447214842270077828) 474362191584396486) 232496483810160660)
|73=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 406619 483678699568822191) 517360600245548744) 939755970407806675) 617420372825367218) 637379562985468585) 295031238006774492) 377316364423122103) 593472412584149351) 987067329503681616) 154024865583807889) 345095314902452877) 150996459245817575) 849347343094880394) 718766076437458762) 435061547167342273) 38092433953243485) 772392013110234559) 385733124544371929) 972233394501940248) 455693539129065588) 88119573032734723)
|74=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 112 61245876738383290) 382393601159157361) 393073517199558936) 942172926883023203) 171198542256012520) 934129172898802383) 895092330040490231) 792083126972970733) 668748456261193113) 285892169698124917)
|_=>0
def stOffB : Nat → Nat → Nat
|4,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 33853 240115462949388469) 207668143907140313) 535717881758525541) 301379579899365748) 766075784727245091) 709523498050358199) 681239375079959527) 711133269081982130) 164685708585042865) 809858182662281535) 809751477845071439) 714647836299378889) 507922856127967610) 237997092397951430) 65026129231872005)
|5,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2357 116756261053325334) 10068067132218741) 307453481615710653) 72145545543808600) 51121609795663337) 972600704309862574) 185801006375200360) 86147669265797914) 461972402672009887) 693512665450664752) 819371468647397363) 722430947725495838) 188358896162250647) 980559746911813105) 409798465222414217) 699674416359025091) 387513937947286627) 665557280985875932) 413427631089258486)
|5,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 3776 147297800019153300) 227966486062497231) 587084325133767850) 385448639340713580) 493324360136459723) 25082518195857435) 214619535657124323) 812365968917143064) 49777773119957060) 500501417741330989) 197103615559857809) 152557012777103278) 994039540283672866) 640666749759485748) 544645992366449624) 193843633580814251) 504509073453608670) 352720585004861017) 943948995029641158)
|5,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 5198 678162238165844696) 775597044781636507) 351236284383725859) 612305855736676803) 273140711361808475) 294885856038990744) 391110991723214928) 500103869659379748) 955394513417427814) 376765393123636679) 474649948882218170) 951836254746055152) 753699420489765594) 853998924661902208) 430887035264946007) 422121322422486124) 734579071115763144) 509355145359284908) 489821105967087510)
|5,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 6628 676380295359215203) 5054673986665390) 273717407749310) 924743397825949049) 533848019624482714) 286776325406836302) 429522992899842964) 341844946801414456) 360172494153907866) 749833725833099649) 805018368259514759) 580199863564738030) 969184656757994224) 639338914340987058) 391187211284767495) 954456743095437042) 88831789340651035) 569825591210418017) 456767924392449894)
|5,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 178387 903969194073574032) 852981218619035788) 937811063887730077) 697507211255789993) 128158369410090528) 728665634756547590) 294733124828164606) 384985281815576706) 651652988019454600) 91609560196911180) 410062605821068017) 405547576984891222)
|6,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 9193 945689013034959113) 727961099158508411) 605446528635114040) 353609524999740228) 145668122979602605) 106415397194347922) 40261446924753316) 608866499118652732) 649316525650847314) 387664742839376937) 729091573069214982) 793637464412872530) 106808738113812307) 995393617829168593) 383305478062643385) 862717601498524293) 819852026381565041) 573570627288037946) 175253848744820407)
|6,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 10847 964515643156794973) 413730628500095343) 755638650905720799) 965645637651300554) 760533234103277235) 763998594009440351) 840921968727173403) 181069684577470156) 640616385205319546) 259079160675634587) 688378587779107741) 459100915602531159) 48003109489792852) 254472516459103253) 694087995164185514) 204319823495671504) 935110222852856068) 43922622216246435) 4383705723345495)
|6,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 12494 515988654181015515) 624576906340012415) 897770605193923449) 344602684401892947) 125836978398056103) 750930691676563221) 824528923549510576) 298733265813801179) 769804051790107454) 374085496070405730) 831480755055860149) 993823379629348655) 336593513387701566) 142508573032407132) 779794683024399785) 130331685195515963) 445278787078776530) 120170261738375222) 92438474073880071)
|6,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 14144 801138474754043425) 112454092176441305) 580965160984605153) 774737934426306803) 972555566207555714) 487521308685875741) 535032930336936488) 512906349283259961) 471114237759471306) 346914956011495964) 836854635205720613) 798686598650105040) 427467410215998286) 557888612735263824) 227594693239984764) 576094243485885076) 202873449430808386) 644401627743603134) 99419239527534999)
|6,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 15791 352611485778263773) 16346558180142969) 455598224886803679) 90864755215303356) 312959145318812185) 364946250438893653) 698137095412543877) 966134096508761888) 315248713678224390) 445732151874426557) 945194437553663730) 15816809935136851) 207465621190195718) 764013493048828490) 593853411517112937) 148195387521032504) 448936367598103496) 864424618654495926) 40714500667927863)
|6,5=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 17437 904084496802484120) 920239024183844633) 247939092909379785) 778836921725179138) 399397832872130309) 925885773844585422) 143514287025679903) 68248255686751074) 167853655623891552) 28201741665443) 642230172643366395) 203060336168062871) 269805161424729056) 724954044110393790) 558723361267741137) 694505571533202395) 348332073714013745) 498187001101301780) 636570697334589639)
|6,6=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 19091 922911126924319980) 606008553525431565) 398131215179986545) 390873034343501911) 793540379387825601) 339361705323593037) 21297376850649073) 463501160811434060) 180914396981450159) 555708085392398078) 655877797407890362) 448234597808315575) 755349103852789150) 255783909971133933) 935262633378559984) 583855026359454524) 767169667039875734) 625059181093476216) 365221251771081815)
|6,7=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 20734 507353417980852039) 264659914964328493) 276259446358315313) 794122238720597595) 398170812794126524) 102481771856377407) 66694223226889810) 332619951016650712) 35790910627950318) 811712392269598030) 400213810546818637) 461425029849092030) 196180734741081781) 212110675885406447) 962013662461842893) 298652008260048652) 653518627423113617) 122530196513207361) 952783455441731591)
|6,8=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 22373 824826720326337603) 47931702362222398) 898692400968846097) 602030593570419188) 188628739638342726) 750746571112138838) 225284100550597926) 660400113730454629) 216781503249221000) 350944639294220470) 875925656887977101) 555986306886890704) 312770183741668060) 574897603057580967) 495937306391782338) 307595256956213018) 775131924716466574) 19164407963394686) 438964734895938423)
|6,9=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 24020 376299731350557756) 644870356529708654) 423534378604819327) 982041586713839679) 585012042329679375) 410629119333268696) 58353865090933659) 957252917332020175) 891767322386571452) 785009113884267797) 830843310586188333) 398556197488195191) 53706862213493706) 699315307111911676) 199422556853134514) 222049747104016797) 339987909063369989) 664390158204390575) 135654921772037879)
|6,10=>(pn (pn (pn (pn (pn (pn (pn 307686541268753 873779558408107838) 81751276707205139) 191627085777997601) 569409657506439426) 67957255820251512) 958021171303061284) 509212348134560391)
|7,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 26507 5041538133394662) 404556258815298639) 363639586749802279) 276500054715083748) 325327854889146131) 79956190110302790) 354417665157250646) 136772906613002023) 394145586181728474) 241638197377220248) 159669914666922825) 346108865578412448) 368740491393097809) 482483092795426088) 16221436101222353) 84821977542418367) 142964117808632065) 731681350708622143) 91772045217865160)
|7,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 28280 734906689631279877) 64622532206850458) 905977935208922628) 938409870837941066) 579140860630143835) 188467726347648161) 165163805113599203) 321368669268992890) 990931871549838587) 699221946526872941) 864160342308593010) 987680261973421343) 681723207917615288) 182637754798003345) 728618640567706495) 492779297546548571) 626552381266045556) 325170458404231885) 870409068874415144)
|7,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 30098 802132324137392231) 588214945050582936) 175239632460167262) 582354222455234614) 748036044412918717) 573608299345869040) 567044463042110459) 57108146463793316) 320014052012123644) 720342874190985312) 684122554448913243) 578138791944037351) 562305994948840678) 907054318969851175) 753036800245674318) 442326264325783938) 321503830766275747) 773048138942645815) 456685943213382120)
|7,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 31883 733014551507635794) 215670628539213525) 883372086755459231) 668233821255945254) 860501595878029955) 60300513797252444) 531812760456525694) 765189461472279633) 967123667011512221) 13967626616913418) 616236767001311216) 187112637948626445) 247261394117452359) 465327737498120624) 329333796455278441) 280939500198414544) 413466780960708372) 40045441945306984) 370789749989701704)
|7,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 33675 897896487607550737) 372233245387746239) 613146100516335782) 53178198784416576) 451245831721028763) 404055726454377405) 466784335094633089) 650694923776535243) 946042925599907633) 172757681988755519) 558291644845605138) 436488501913182339) 516345043880988076) 301867626986219188) 597266840963048531) 538735877683525031) 389944970760892236) 370100656809106464) 958270844388382264)
|7,5=>(pn (pn 3242540710288 456539896405213201) 514572162095002679)
|8,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 335829935552 618539743906379894) 921247356553069704) 482764421236970933) 341508140671690043) 625086321442723386) 549154273429155880) 270678378254742954) 56033760779577594) 859282462580778394) 359650112632300739) 599381095409545633) 887877717777920297) 568713746507652454) 313119274146836409) 359442598497761400)
|9,0=>(pn (pn 49 433126156888536682) 37153502320283766)
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
|0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 774815626 632332684643119009) 252046060317223338) 854125315083577066) 36227784455277075) 660812080728052698) 772199615321216284) 513409641112925953) 698528359783650434) 415255566272104929) 67528769244350418) 761912957883036490) 675703385873854047) 832998439979694167) 441597676916462010) 369372952939643846) 298153337573744749) 737737751319796296) 372915283609545266) 765334877327861094) 758075504230688202) 176273198722182201) 947692752352811071) 546724831985713233)
|1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 42619850 451485934718208385) 245187330388436992) 257590931168619407) 669942293253555912) 488569857649549181) 469223985704019872) 852689072239640257) 484916573450202188) 202943463084795014) 457361761530038206) 312757801464252256) 666506589943690964) 961238959732483149) 53375930733815286) 500045654215402809) 18931105401505918) 204354712417368230) 122225780148034282) 181653336140104454) 949650541945920471) 213211371583976765) 101251652850913423) 637118563805237275)
|2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186902748 590728900157640968) 812508002420435377) 851739612905596665) 758382483479775736) 931411700807121532) 914245888117569065) 40144758473736377) 654687993845107077) 280398487244730455) 697567092514451306) 70226782203003542) 768318351428489934) 660724932199698158) 579988341687468167) 51431788257480328) 891022490443488322) 282179706435523397) 903851159824751177) 594147633665339623) 529509374568436561) 893379040460763715) 768351410449512106) 263456845133886104)
|3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41586315 85251135145034530) 946353808646730596) 547229772408263402) 132443595141431645) 538212154545531225) 238938036272661994) 909762036680162808) 657618910059080430) 563479501228200311) 802664364979461600) 223550761790138826) 313116850531024125) 769693022901712079) 843648210056991308) 495643502617734933) 443210125296450828) 75979535773538894) 546802957539400537) 534942710318724664) 877621086692488349) 633908936052764197) 541505404954813176) 659466538312642577)
|4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 187426284 746794065605790910) 328280480473030116) 317795291007703422) 156927629425862664) 492043191765871831) 707322607342037412) 257977964667743245) 939675280745518072) 62613641886451918) 203260512778931944) 852607406169766947) 229180490283724793) 257006476669152951) 454228285925469111) 316136338173195403) 900443717282674125) 813700601892447518) 405274932957882002) 818225211162581490) 328560707129657956) 716139623807468582) 273405244390568670) 864292320685175023)
|5=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 42135464 633426339710071088) 972523524755923443) 71849659732996409) 527393646606455048) 757510744406821454) 931847498428379127) 961877169950772715) 907151386467652169) 222311023374569356) 476728967451004161) 511098707598125313) 67103428391927526) 966863446060478465) 394661988890541912) 415711044163752403) 289135160443971723) 522399601331847323) 969596839805289935) 627338060378153741) 225785190076351752) 679441393330236229) 762964657437077171) 278768834336538705)
|6=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 189142079 409468200072847216) 123604686067707248) 659245642832122522) 913010099068604778) 29743066905709351) 657837514097487977) 638864498165561495) 439152223753495603) 939879939550572657) 604664449755893140) 85489882656649201) 736501667071197233) 465511140912572752) 803100958348526321) 201330598775259456) 880010847864401832) 152879194717417652) 568303961466753362) 688722294419478037) 548486835089366525) 310056024015445764) 789495913099354851) 311762280080785782)
|7=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 408364760 429112532993546907) 981212047179020242) 14999950089886397) 872925384218549878) 853095703503268810) 41444461019592914) 599651387517140897) 94747456626264260) 940632629398934758) 887442271329743090) 745024680433336769) 913795570222735327) 186828341237914475) 855942651747969552) 325684924117683817) 671959689007744773) 748435009953084500) 123142535039653528) 37878528427615057) 129788746156362926) 438683449500386292) 235004436547731006) 265562184657420369)
|8=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 21125008 318129027845097004) 382332478490798957) 116654997201386888) 78723308794704607) 746083701519545516) 471376482023149305) 818573442402076947) 491063085347472284) 587574425202719816) 798431875919265226) 239558207553099759) 173578176465483839) 74710881642601475) 35625542678837756) 42972833822930220) 220669760889578422) 157828013497422570) 762744727472093839) 65557950578438464) 601534444280696279) 791600716579078427) 651550804202039536) 812967850711990297)
|9=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 996113811 873091377962000548) 813527503614915768) 539258273728688894) 152842268643387945) 974198693472288475) 643530991127469001) 733902039804676262) 20241266046601948) 362772650900215612) 728991947375570934) 777492893935136022) 132078839013915991) 805594173634263355) 85725430770759577) 256431156378925409) 920976342211289899) 292121074522147955) 125575691002498368) 988656373658227991) 102162797350332888) 264081253906388881) 546405382889842895) 760526102835081297)
|10=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2794653065 179355528239324754) 367968248880302634) 418950951820009442) 302022200028951604) 379294083828659657) 493368210285231140) 979530198213610052) 428443387238198473) 554973161287905707) 930083176487828785) 186211074393653753) 384567740108181866) 678877265623628994) 27526465242950437) 837081591972097613) 98818375409694595) 816824078686011187) 394166760144380845) 137267614928594) 516144552928134029) 902435550587650057) 994237536840272847) 59479496400879697)
|11=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 22915148 577307733652243156) 136039184253355878) 156826741760867098) 258207077804880909) 774571467594855405) 297352061383822881) 745166221153960620) 63673843395328049) 73126423323967373) 652943646297309990) 914106434567101097) 789989571936069064) 762083240875483243) 971189077293775681) 88759532617953359) 633511449374104974) 569250971364047840) 383852787667917353) 885814527971314575) 949162426081784482) 582981395358544401) 627759635747703701) 434905738097045555)
|12=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1232405040 84597935240858595) 180325688112425535) 108604430053128828) 949759122084112257) 529858821556277069) 417461760054014017) 783436562801306072) 116597325428051825) 438612645522657153) 149486308046936521) 358732252777438699) 731832892376064789) 6906124927547814) 928010082863845113) 38290656658018524) 346824802222280006) 334616951183241117) 763751268809597101) 206313322266708999) 764752267269979286) 74871112932315255) 853726474552516415) 882793620709859409)
|13=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 172956813 583257945630775015) 647449405339230630) 460989713056540477) 856873719763927243) 483227191802879104) 77007406743449613) 941750759779282969) 320100002109138373) 891546660423742419) 12320688247500289) 660504355490359519) 148880927794825585) 614544741616583294) 964750653210427707) 768670431043237894) 337113509785553462) 29360909612164232) 225914885696021293) 572809160439076871) 928404045622311354) 339918012936443831) 313876327627061386) 494274529810034713)
|14=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 139415857 328967674916035744) 610481412637784384) 140623706749603391) 597475886393324294) 719652881076534153) 198687235615383567) 355133006444247643) 476034058961665238) 686551393917711412) 512549807971626965) 51460204070762692) 638855807341749039) 296017492055123253) 760949999798172739) 651742428944770440) 955242900590985046) 875458966432313441) 182015136017425006) 699004370314638850) 944510263625697885) 536073701619509046) 168227016883941376) 630902122883399729)
|15=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2677118807 661708927577232717) 408483793160029520) 964477259793122755) 510003231054056650) 846496806621372500) 23565399108142265) 463881511493527172) 47106970306875147) 894111110723061862) 60683977342368903) 927080317367252724) 361734344678814929) 403056130558104220) 41726318214907740) 802981425709632997) 986309621446685005) 10935157864412215) 864284616667829423) 440424450782514908) 270166205280258272) 781547395756976628) 592823985651086172) 771476911935275057)
|16=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 3209783112 13059736841548793) 972904586324554522) 305302091394231358) 500102047576718567) 610505573294321089) 890532159352769601) 952583011198039095) 329252406459101361) 609093778583128216) 693924854423888355) 881129037160389211) 745865478040379013) 325281910401921202) 55061421653165859) 972691444540414100) 711184280560362179) 202911905858614515) 528024725917390252) 759924555324573856) 318927703738349603) 114600582525416403) 367350523689792425) 411947685012881489)
|17=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 86413461 651857921944882219) 875224891647423611) 338497523854488046) 904445069737667670) 781782067988219253) 518023501800272808) 35922576655342998) 950513460638271199) 633235858394470900) 892820880951236912) 992924936891895935) 240453265708290762) 262462002904674110) 855635046402165611) 911940751848779003) 268060485546944519) 323040849509478762) 607319198858508704) 999825623478170278) 326046440684329152) 971673515272862064) 752752771034838876) 783389366785425489)
|18=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 85663560 483176462172104460) 942269911020558881) 628360479575395650) 992991396409948197) 943252152938890655) 120328046833801574) 204850285785627411) 828569823267049456) 548557463548788963) 613612158489545281) 703133189390569813) 981477949218458382) 783126625981571576) 242342480716664081) 612788395885611002) 61910319852526221) 49672132188187109) 576211394885956800) 734267073311773311) 753849747530412690) 816646795244029836) 35887400241877979) 962873009733132337)
|19=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41640651 40042179974271199) 586533375742530049) 96169142915632420) 530251798663566244) 356719281419529962) 957590114463352170) 219572932485783830) 589018701736837088) 432157836548132217) 482076995959356395) 152227281331794183) 496188238973443616) 463452571951126042) 24057323642602930) 595661953698480953) 814902976749727656) 707162779542091369) 22752543805083646) 277490902329520537) 421082610421277719) 673119717695852593) 869742514337489195) 407091479059972145)
|20=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186906144 277288521746598421) 554991957491645526) 26471912660530196) 119171727132898174) 996403537372103166) 703211988859721814) 957426351357623233) 178422247710034750) 13122655857521981) 155572677371976444) 821596192659302816) 988654820776993459) 424881396773512520) 345301783463364108) 90827930860576932) 902145425831315896) 381764998184531142) 782828133408920514) 605167946246112140) 674067612506659780) 498104481975771921) 513042850599952640) 902854830635114545)
|21=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1231357953 42319329061510110) 313784018258592283) 143133970900462617) 533523675762617915) 316254394317962522) 764182193368996785) 422818221953825026) 580389241498738770) 218245539561754376) 565584371630553657) 841792702050875522) 182191865786824219) 443835323922509858) 731377245395883367) 713076979312940178) 36105491177497629) 572950617328421053) 846780496481524203) 978247468181519058) 12147777434873366) 848616591161962452) 202941721875713567) 104791685101568025)
|22=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 581078377 727577776792040409) 176941198264338632) 440294192081715654) 146617965096783327) 296811263773405502) 942529176077682812) 949972849587216495) 980404370113794805) 822023746524931556) 996476328635077709) 630141344049623154) 645866556807394600) 122867603307589213) 783454652435020508) 543916888252524395) 837173170676459254) 140198206127291562) 37814738476762066) 328843719600811476) 966131991152090195) 876849620466310292) 160493883250184907) 800411417230729297)
|23=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186808173 401347658038002732) 691401489121668990) 429740433373677140) 321678512772475702) 726180671395481796) 671105444923406157) 694057097812708841) 769160234393204857) 633226043684069268) 839414310290160632) 831508118627500770) 424487195926223749) 584587063022932921) 457176264371671488) 601266464609978920) 576896480301744950) 618193565443501846) 737065296803036143) 138993553639606438) 513222196106454845) 11329899662602999) 893616348486107870) 213644206479532081)
|24=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186808180 493402378152588739) 90304423316804815) 538944580645231708) 380419245815386849) 875732197453579588) 473719028905761973) 640777194157986222) 483509654359353689) 130463786895852698) 316174452922880048) 727688571629048369) 140965618755280364) 790370516869413650) 31628672884942575) 408742396375538049) 966876185760332898) 146411805440780514) 462811991317399431) 195689718661940748) 969589037510281941) 907328094112184702) 372062407076951471) 753094344166424625)
|25=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 142305352 762832933040759651) 871063870636193532) 412766774855250313) 139371783827260098) 382692744986379628) 918474630550080015) 841619385061884474) 105790808724985081) 10382839345984471) 661743447144148864) 724873391893330913) 985723435489384089) 194501922426384720) 674605993215190517) 6615583712213400) 112193082856175790) 655278696589610600) 497582607923958546) 405864336141344208) 952201340697654407) 663167357288516006) 474112771418217159) 307682172343697433)
|26=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 63354759 461582032017669980) 373187009886566817) 782968067886914029) 952124545012575242) 5746763504140440) 476791091535923232) 449912510046422646) 864913030328018917) 82996785431252864) 551411764852160953) 364968925383862530) 7367001496300963) 633111776431350828) 84692215305362125) 389363341096643304) 334976609004727391) 153658011971952238) 68548709797790478) 816102408533039301) 855835635839038623) 857912664971221467) 640210302144139953) 933617130700300337)
|27=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41836259 746393050466230461) 562025000247589121) 129203602061780780) 60288986507236844) 178905222056563897) 837486775533335789) 638793847665252666) 606140902576560672) 154433333997129584) 433267462311800821) 267551212011540149) 376919568341091089) 440084999874734059) 494154429092812117) 68531185108213042) 988444022324895062) 28553561634506672) 820609483290347994) 216598386149418619) 739450156126687609) 273899117875199117) 310135038324145996) 85808239975882801)
|28=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 188542556 351113399593690026) 36365134704663460) 797675999245049439) 17454393205016313) 326186788693576932) 419575943193712235) 181607012441940084) 596709673240138600) 586632252232749949) 644777513109975957) 570276511129838545) 322645398689313949) 384532310966179607) 415697185524800730) 392931868393861838) 303407719367331497) 637697625965994000) 46285178209310750) 284598514511975202) 747006822305875353) 914799620074735482) 426080390820470303) 65914730981965849)
|29=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 105231525 190190390581966659) 678900589203671998) 66188627735098260) 427366478649906352) 405207281373362930) 141941269980902518) 530335701171886625) 372181998115965503) 3647022944302920) 846825438071789155) 868505635431942734) 501411431886132192) 645508595328210123) 550404370425178508) 653922878128172765) 632362447358147036) 581876967467070740) 153698739988556829) 846959393034132138) 181504589460931007) 975268555700169206) 448585598837799963) 395036566016573465)
|30=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1321331285 853352688801266501) 829903643530332334) 244523385644083752) 625646908122006942) 396155682514402280) 326057989973578779) 859675921615387554) 420981636133287863) 265748583292543814) 8104489019406547) 532351627058891023) 562777505663238967) 295062637500773299) 830464493207008953) 339863165448537763) 576613196992388647) 69432843423772821) 241132968074609614) 248028355955234457) 548671469184009862) 953732033434053241) 69737844727896067) 25724271444910129)
|31=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 28285480 232661310747959589) 677461448496008565) 68028410464465583) 878405796516304236) 901260664402577625) 479528161746080300) 332794036797367147) 9992171286407546) 409470064145140404) 28257374045005925) 91933077987978329) 501163375372015513) 15626677917328136) 142252205091557151) 844248751048760659) 787997740543561405) 927682807462732790) 249810255367962802) 76062348424858374) 675487736386806493) 587564619881832433) 912637071019867214) 67563909708005401)
|32=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 83672868 967119188932260213) 532454310574838044) 721686283695839563) 727978713973491940) 66290438295526879) 267265109424216511) 3693595353344742) 881870013113071848) 443419658376329417) 611471587441671850) 3353819796473051) 553483643326718899) 735227665852262408) 302215473783416896) 328971887226369307) 153750108666883520) 311081708938202991) 231649160564377194) 934361236739233942) 794185264410358242) 838188335338812902) 558013053938913632) 82187973055004753)
|33=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2677166248 593983920791760651) 69767980480332772) 42920853647643474) 680175927261452294) 917685810667286996) 309967778891485233) 495052166570301752) 667782354803402555) 113912707453812898) 479945170069898974) 993565142973980385) 830541222785133988) 64528055434205883) 630583189682981554) 948297985358507922) 439004943979909774) 984563055905201046) 175004053547925765) 432601089459756455) 481794847679363919) 339081419454567646) 559785255164277574) 872844652844728345)
|34=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 512387159 469068491110035969) 450689082432192434) 832503160390938181) 509033002864057918) 884496636532172036) 797451617650598907) 438437296670534481) 645102323670593834) 472438564701202232) 885150321364532622) 374642938156933043) 419265683838514614) 352232424138366340) 685733406401386322) 664565119050257629) 633801028726875526) 832378731584174137) 888134639557481496) 386262900353506036) 129300948242758473) 560020300054221142) 377182779246794863) 25215943171137585)
|35=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 83974772 209046329756769456) 227639844245258284) 531269576708065840) 639143680042206725) 306098986343587000) 857972338640318111) 161053547145336703) 661120958804127356) 936669547592642987) 871068375175860415) 131586869186505158) 817042136323013870) 127425377617289931) 910308813771415306) 521825749602762175) 643371866527722755) 603248101715883918) 586498704121292324) 815618435429984572) 520799096654131847) 811558985359609166) 341524313329936171) 117687793575313489)
|36=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 27751813 269667895047895276) 69835687168118268) 203698487873920133) 240384392521074120) 706075908369021971) 130626691076817872) 284000964155173689) 299534494817833481) 566597262790313357) 399196641400738496) 163465643039566089) 567581482552788656) 560272894637780022) 562503232185087581) 795269828161904644) 321364277423584985) 829121835995544302) 455892451170241144) 854735428930807418) 398422511746016749) 407948611493292165) 709969822745483986) 308566795516141617)
|37=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41917303 140720902915316745) 287684709851156560) 816286656695284414) 3288154232199041) 708526034597738521) 879609734902710466) 116886715254499961) 221489988798361757) 804781395376850818) 62332483275816028) 615031995646806068) 508987120047345716) 900914072548080736) 568406971357212329) 871763421611722781) 873071596689374710) 344096698318947776) 37453120725581942) 733538708615373337) 907732808180048205) 928614034068926845) 790014301938430039) 307233929692557337)
|38=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 62338082 74893897842937536) 972692840588663468) 189097456917354890) 812846496564033055) 860365667321106291) 77244178823162090) 635066717692104300) 626719064998040111) 515550111254292603) 136298650269474555) 733317440182603836) 172613455587392923) 788394440238011708) 523021416974265214) 507447728909211229) 294020142034046610) 115664070146727323) 652291480676544140) 4306610970167261) 514489322296184741) 446208015455190261) 360873799516957129) 782221084496904275)
|39=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41641457 487262191119174053) 846586097610401595) 860837668181878469) 214696986469794528) 410326500155783651) 766125943894879744) 261191395703076084) 669833775010357442) 22151259078354052) 351935302470145190) 671611502791276852) 388217198975777500) 921101751278138818) 117331163427112133) 36201232835351966) 772457071520411270) 449524120154420837) 458718626892817685) 36552677046419809) 614262283351912237) 490725002380408335) 609230582652608149) 288448809087643729)
|40=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186808175 49742314526857964) 944639850767931070) 246814979200629042) 893659650492207450) 262191013267040229) 533865951517545465) 189837185987757967) 413987593561449630) 371249451495697438) 431507968644613322) 283251445384189947) 925944548877544800) 93724338192340990) 735903994327081268) 818477594896675941) 788329055321658396) 404032530149112175) 266572296387181013) 301520057872253882) 808344768041494017) 876916778666281771) 826488380609488582) 771217911383113809)
|41=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186794692 897091710380629443) 94893152852805540) 678389995101813305) 338288402053032765) 116338391798277180) 218487092835467247) 940842717560419766) 108355793565339544) 681077423026568539) 37623938740558581) 33857536049082993) 928737714544922111) 654588558248662622) 480128906693066227) 927840941072741299) 535581018594228853) 421377267800360058) 846558685445407151) 628226024771059626) 868760169278103604) 547454723540611186) 489078188825569081) 582219206166876243)
|42=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 83049353 245266615241892472) 891048820033664818) 341213346748638431) 245809459897951521) 978992377934027043) 789698963684911678) 623483354238431499) 507155314019039409) 946443645952599490) 811445613448954606) 194659886600279602) 129504028520639512) 10495584452590963) 738116624437881173) 840437451915680490) 524440318415898374) 357832791610123417) 499914193313845907) 156781507383152623) 547637413481806602) 339567624336193765) 992785395338426389) 212472648612724817)
|43=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186787914 594752211603137696) 164180000157808902) 886976560284692713) 162619787116180245) 1500594096075076) 354482309638091309) 672222589814005779) 195849607602496780) 660675900613968385) 396293374942334702) 150491497122618437) 380382887415409728) 34480564864143123) 496922183538275560) 648890783575487248) 185224368879469371) 239022115100807219) 563658214148857325) 761537162099061079) 267103427508379787) 965365355737591497) 911287062952345344) 111682942618677487)
|44=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 402334149 1853151244421501) 253779516245594118) 653108640353306723) 179998758418614069) 276160140274687675) 189893749234429819) 86483562209497696) 266744106024984481) 122376600302011709) 519966884954921849) 869091376558063169) 256648809895983667) 16119501330175076) 521270989975491860) 416421157698312380) 306710949707750708) 431237640170266266) 154839589318862332) 889766327082106112) 9415791087266791) 864465684513088534) 691299432038410682) 130231282995863791)
|45=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186848715 750182757074604850) 803015079854239155) 331774564100528725) 377384647314801540) 925506857193752607) 89216759838612433) 723249490127360478) 632163971621522726) 279472012530057269) 104411026887465524) 828666966354387817) 99868899357285186) 361365885044988014) 853133318089371713) 871807617509346860) 353221218749761146) 664919728911959438) 259614848151307897) 52210114620671702) 524526575221768378) 892434260298722846) 224460913200789080) 599547027937931313)
|46=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186848707 504176399776485313) 431740254277741173) 894954742957267251) 943069330630004242) 3263151138138665) 101688985346396636) 716377431920675991) 340211316071686336) 63914108744138604) 251178686932718075) 710634188301617613) 403417666397824183) 757699249684598012) 537573699560319840) 409565450457527208) 381607764654344037) 341959255286389454) 896264954265443270) 371191436143902621) 687043209704873068) 86732920809503829) 802482394249605934) 346047065635745873)
|47=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 410078910 354743211352507765) 33549962891715018) 15485901872362763) 749649069178411742) 830004327510310980) 502562005003091953) 245441833933324376) 875792443923448711) 91616926887718140) 480617939196488631) 576770177111843993) 525801416660250174) 363050760400629604) 968013859268124916) 823173954199668855) 543110756453657967) 112397671413903515) 980871391458520071) 267360593973072647) 887340899407287873) 550123833290727398) 63045812322102093) 917975497335222353)
|48=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186848745 435838215477291824) 189531059529702004) 578447612198665487) 437650740827968047) 825620429227373201) 230773111598910272) 211875093242921781) 702040684671806470) 358576647309338872) 696124789284163488) 740683878466454418) 312591553005103421) 932345236749263491) 586498958486935157) 608209671456633342) 470495506667571151) 262551775259031769) 903691842838701478) 419470566137721911) 998860600918153977) 478835758722497125) 719377028680591830) 115224330671513649)
|49=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186852123 15816783384976951) 746218718460463193) 26251181208027371) 840521306640908511) 358328932092054280) 787176238356377655) 14498744857843913) 752413452473829923) 176328458444829939) 406646546618238694) 706425611674335308) 236559295034244026) 843953215390958279) 829609413384802572) 408454228199441447) 614664062414002742) 493197262736600599) 927825813804865507) 385148993423194703) 256621415556685424) 854606637047509059) 402151241271232352) 834231497740316685)
|50=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 187703269 986416611908629382) 653338843320839869) 993596667790029042) 711737479869916108) 677549710315977644) 596928541729932359) 466818556301145673) 912438587931043798) 395339175068033059) 407598380913934131) 917592310694818858) 737350606709526499) 670128573821987222) 955000232101255326) 822807261590595765) 645593256459781150) 994631247996954088) 382564775154043861) 913429713870339624) 616675981821962756) 940993937414964059) 309960269790771507) 165628444906119837)
|51=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 41586339 598237908138230046) 836405944252891327) 477542559809850674) 825214012804852751) 940968198129133742) 649474049216143697) 335569129829852842) 866478915569162997) 173356786659913028) 658905685401761522) 748531801616059347) 614760725848937000) 290284699553436181) 210568450996605308) 469725860880944598) 183225329225814945) 635030234680808395) 8110274090114) 226039392771684202) 197554992821610781) 145734757488934600) 910218872503088612) 674779903533625369)
|52=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 186852085 84154948290575489) 357655932981509035) 415685339773216191) 160072921508905430) 7600044769209244) 518698678106220220) 849257209489450654) 248238776877910689) 608917036716707116) 907678312343314822) 66158105900135805) 705693477879434592) 603640881795532697) 983114774078554925) 37460237205511595) 487633298549507042) 821587239092375011) 848250256852352084) 285666344578408160) 177817755340766799) 486646757443661541) 564156510359067434) 903051332814483693)
|53=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 24680368991468 112506028414945092) 270455094155200856) 116465512843763315) 323727989947381488) 384509915139554657) 727852648082584282) 32652598963919224) 655097672100252228) 139911600796739562) 878988183377001877) 543033641500353072) 210162148099552277) 42000528641800490) 77447772052888146) 337751216661146621) 493711381630590390) 35623984852291873) 583689275929449669) 996615849031524401)
|_=>0
def opOffB : Nat → Nat → Nat
|4,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2151 129126289055930053) 182062514465448412) 406861341626297839) 770144437685601411) 507414870686439950) 321449047295282369) 408865728390849885) 92034802106099109) 138735370483415355) 766821481231957799) 833229006219642613) 841099304562851840)
|5,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1178361319 228528697858637866) 508238312644227514) 844624470158709129) 324953897311581338) 505316918889660542) 36302346422270242) 388048739753901927) 951487981794223769) 463928131114534908) 302260001487625373) 555185194723768672) 54965634670817667) 857054250342735217) 443687897219208238) 412928489380230051) 513563453765713920)
|5,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 9 230403745745413223) 411236201435758023) 469849880545166478) 217103037237590959) 485687219636352424) 91181744432100251) 151342180815546125) 713131119276060284) 708993781629364559) 733865426404876757) 942487625044999041) 869547207257126354) 277579241929071041) 469732523345578000) 567758343107044958) 657665875297116908) 278584611622422405)
|5,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2327 137410184602026036) 855423629087199949) 513772037542311524) 921771381678167051) 372892878009541792) 290710836976109999) 293479067233949317) 337641479888151806) 517347291140366160) 682337774202758222) 322271095130764163) 488478945778550283) 837986930482254542) 37720411982175809) 494398198507110400)
|5,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 231253322502443 193707699885466315) 889268101502978839) 119680621198501929) 732989007408549424) 338348260346542035) 765483457078712934) 488832723494816460) 815278166375572889) 700546278044341199) 747394699197149719) 303030649097362691) 133719534175048163) 306186699873269356) 128459386429158480) 159976717508699548) 637836297151774720)
|5,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn 5 557740186919386896) 893814241536554334) 660837349676853787) 589895632400801560) 704606197594701770) 923603687942579266) 66409718596729631) 946476847650632537) 963062835565041125)
|6,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 24 588808076333399411) 647807737812891761) 657870343858047790) 5474078420541035) 752657055346115067) 867884655917475766) 782241822571322218) 129315275526025719) 925349267270165240) 708022977213763715) 889977020476512743) 548267268737015910) 789685949027659049) 584316741594345298) 847209966910593640) 163891013584834669) 984953299003244544)
|6,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 33 367113049330465497) 375296447678245360) 910398396505549046) 178059395772377377) 505489743151079482) 648678908758772580) 703509284104359709) 825083635808912833) 385772530995254938) 69444729695226944) 849107487309962950) 310912013793384340) 493773694668507671) 790535019854256486) 615510789795054824) 380533495549218381) 846055171655738180)
|6,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 624321187050613 171419273335565011) 515695466662900076) 671452893679373906) 412435029222411107) 694695060646357059) 733708895528127195) 935166731809747069) 630534754881421728) 542230932485842039) 685438557492609787) 755436842590855738) 59810407188478705) 319001108493436275) 460266055710929242) 525919847557230004) 528407518849806276)
|6,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 50 220743354654443425) 703142553209648464) 540726503521009489) 865178002316770516) 844201963542506681) 34369113371552457) 712542578015006130) 819306758549859493) 234775832389021118) 614151158227334662) 831190908055863564) 203510963973303771) 850160322904287091) 85930686092601831) 109209011039187853) 960511417910762691) 929823245729282692)
|6,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 58 647558493743441574) 969026616947722296) 391403772782026901) 949602159729883209) 609169825462916809) 94477133166903515) 352738837024972133) 854257142983430175) 36342619274807966) 252843538047784580) 978017031324289126) 956364323102938551) 997128593135980717) 903944329628492794) 471264275728370724) 169228795847684554) 852933456959111168)
|6,5=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1012743057246072 969295026055425840) 655948120213224615) 908314246745336594) 166676455548819753) 226989947223493706) 192204944712908450) 771090850624229809) 335082421888347069) 159246076680776578) 594302659136520963) 123160776603385660) 304059025969405826) 42786612530595013) 793702348785874795) 337454160019323998) 199783470804259780)
|6,6=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 74 974512865599036014) 561687130348463045) 380490433732841043) 653537704739677559) 640895069441649776) 724949903703286367) 345470311917707186) 431221177056091124) 351355420605171410) 60268623198288627) 845654027096425789) 97559794101034145) 566431143536117622) 633628069295195448) 971423044209402493) 434078956625553653) 595254241460510404)
|6,7=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 19254883146 619661596402890107) 883234123181474567) 332213625429609931) 341299975213919041) 721393924829654882) 694519979934711531) 970389815703716637) 5286733492606041) 124660631318640470) 466985654126144659) 626525438077465849) 940085459349063867) 916705443586044995) 919726982957646392) 413809539116799423) 57773586481965828)
|6,8=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 91 477025872895431072) 11141661574263797) 545462093190727397) 204291321441816136) 410226217792096136) 548087937389293131) 532955801664613332) 102802822516065604) 744562038074561479) 405579739801262440) 890714910333083918) 198772442522489016) 586405750513958970) 701632288372052287) 354308141688616083) 577365807286825352) 197608777826959360)
|6,9=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1527090449135913 261021402332754542) 919923324993055191) 817361971075693094) 608421119896015172) 43504546008538314) 211597189301798395) 521847727583686439) 44193187273895161) 507383192760903958) 319367479240845209) 167447355473782503) 513845604489522202) 541270796567472651) 74463972364287128) 53368223654149623) 515087334656704512)
|6,10=>(pn (pn (pn (pn (pn (pn 97021770332442083 988073325967722374) 502487235435065067) 670765247061127329) 419358453047425890) 181905976996620135) 160760447291883520)
|7,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 111 531859088543579597) 55075748778725219) 90553444399197245) 172497823288103605) 9009696264314030) 592564648633255812) 198927866269063045) 194513889043986231) 504663738199122068) 69844258024386527) 164693703782779701) 151768881593271725) 722564603476355198) 954178917352081117) 426233342291090366) 898045385188587386) 858323372655481603)
|7,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 119 958674241205568562) 561180190838516142) 527534110166750142) 768854111020685890) 421368874469554624) 693975355230966803) 866966630207840830) 649581987988031814) 886436295002181547) 258082402081284374) 400751199794604830) 789806649773967091) 540770997708015958) 259520817424905803) 666697568263596556) 231066259678378925) 32041913978691331)
|7,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 128 253820407107213950) 481251750991122832) 785811953031685026) 340267331757446577) 624159940515338334) 512551519538088561) 290192288460075213) 206914647886076686) 27868655605193222) 84004325137293192) 773745297431245192) 777250077826839092) 267729869882466765) 665458598029019542) 630955488943809650) 520264287174345813) 627084889841183491)
|7,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 136 680635559769202915) 987356193050913756) 222792618799237923) 936623619490028863) 36519118720578928) 613962226135799552) 958231052398852998) 661982746830122269) 409641212408252701) 272242469194191040) 9802793443070322) 415287846007534458) 86274311261467777) 506058650381917290) 425118766677788525) 688779557494059008) 595514644416935635)
|7,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 145 107450712431191881) 493460635110704679) 659773284566790821) 532979907222611148) 448878296925819522) 715372932733510544) 626269816337630784) 117050845774167852) 791413769211312180) 460480613251088887) 245860289454895452) 53325614188229823) 904480705493128536) 811400550454741976) 665582992650294715) 21800431983850546) 769233185740145363)
|7,5=>(pn (pn 18147875 575631858037750448) 511802429445230291)
|8,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 24039461212653611 538787775915433370) 839357155581484840) 617201016985272488) 698759636970556664) 258563071935513605) 938729725472241428) 162592232910959154) 11797840304356624) 185881105100323826) 538557375476629957) 110804335460492318) 427443072638602158) 248594428278263938)
|9,0=>(pn 4367202164822282 602818857766868736)
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
|4,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 246006326 109391223394875032) 28864702872981045) 610960588041235502) 310532158627171755) 346707666979413767) 639498229024959606) 481209772867678427) 55655849278369042) 346056494862286348) 45511778581622677) 362019620800321140) 437501187752551797) 839798882395102004) 531956449152073728)
|5,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2428731 676999500958982484) 394842893893550675) 977777920056096994) 347053423141744196) 668257316084365331) 851107815113414633) 202498778203570180) 749437181240791020) 448567684360033189) 225376975018154480) 345932788968552661) 780957972111014325) 914933409574647804) 863059181032047029) 701076680607480491) 40134227408626295) 855504436823895282) 800610608733601948) 398600599762103162) 544407229065121139) 995670950893713133) 508699461685674038) 421300284786727354) 267400948066320843) 360590601397747508) 820144235857091904) 935532856624551047) 339843127637293254) 607335787577716688) 664719112423539917) 693911820361246989) 507385278753865770) 499490014514444375) 751800021296853701) 604643738641296741) 716493304706994379) 153208224395123619) 4635739021774243) 501350959364449998) 91102812440100864)
|5,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1214514 76517145443278624) 725662991346712634) 257339091496717970) 972454049571071305) 32505559803631166) 840328537501908403) 222454788959142758) 527261552798692278) 936221638761491202) 309939485264281429) 409454183950009534) 202252671343420330) 447188718878681052) 271842653164326055) 111360960300856269) 109516933517737275) 616168239238803854) 839225619024066557) 874713315810656695) 36135536030413123) 816040659992176701) 729944202202963273) 855326464538281457) 275656046176990355) 919816695815924626) 318857558527624492) 352429781551204598) 264805265153142090) 231660852780550005) 952429297264747512) 244386720129136324) 755622163260187203) 454730751989272524) 150967312996857024) 21254254458969779) 883050453111192243) 148720126838574051) 144741552097035735) 533503056987681906) 389022401540128768)
|5,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 2784692759 789302539622006578) 141161322546531868) 757671840909162093) 486883052679604034) 666423289813269446) 793568601278617829) 100461489246591306) 450721193732844322) 673816385517215593) 441815753373253664)
|6,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 39792643387 492111855012044246) 714740843551135137) 130917293149709697) 311561653635287386) 229767120647691653) 795222320708856496) 966326904163940163) 361919510188071170) 434516083074525316) 34761760367130258) 451859262224902778) 312220834676218585) 775759645545778624) 793217927516406931) 781951795764733904) 356574834194286914) 10628089253603760) 108548901490931788) 50260042515112381) 131688954311970715) 273397849381121393) 407955904829415992) 779517740622662274) 104174984991754100) 248668084375555833) 625190762980924638) 272777514190392665) 69341467397102412) 338462209288718782) 310685288702252065) 441368237572113266) 73595980736101948) 672685554731569306) 549096884066070260) 157134911729244210) 118513462323030766) 196132116913536181) 858767371487586271) 446603736356038644) 951085255561314304)
|6,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 9715076 140315831888359566) 917963906149885563) 848006176260499359) 927448077905896081) 557530741680166858) 135981034603925834) 86439787897908260) 465607324876466651) 877837135557567377) 398309649828613629) 550211593240577405) 947673839815554929) 351976468018686619) 781745332084641653) 867382253873666601) 854758915615276497) 799503816347253526) 430856573358313330) 512669838273341598) 51946208671241458) 999443860746362888) 160055153677365178) 278641524866508507) 34423504256686893) 769708616756757032) 169234876707003672) 720875023778709023) 18270951909221948) 209381441013099570) 24119231312166578) 897687156507602384) 902182255168970320) 748153770056906446) 81135493086644456) 962529415402428799) 917507859077456089) 738515326312281527) 105119113039725075) 964069593805498049) 434504343465230352)
|6,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 166 767769569430111336) 890615692892091013) 981218752438489574) 225093000732035847) 992876367626854628) 331115134893414266) 745095017597497065) 628423297701679504) 108250956531967212) 469482586502688036) 666655378090937517) 68060699797447807) 373583486506263094) 112370431049231585) 613764385770651214) 415862942076256164) 684997695551729200) 199353379764398599) 530611536464688678) 185929286739773770) 665658751335943303) 129478277060293549) 513102277417967149) 565806446786951146) 906145578668196797) 606431371106518650) 964566942838484067) 497029337511849876) 827955878629322870) 323492611822996494) 10174790146515157) 124923467949858229) 741320713060148770) 574781272262026257) 769598777557576929) 481265084928332558) 552174353236132545) 338290172095122428) 580782873378306364) 342154272530497536)
|6,3=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 9197937051872419 560001256137535952) 350627255196580871) 865505563296120081) 661887217403503141) 994101403724372472) 570538618483944998) 46231292403003166) 600854433414828961) 908885672070040419) 739411250398820664) 775486591451385326) 650272400832960666) 924880612503035375) 749607714994846983) 710005308223201551) 231479572933564075) 424187631504903032) 123139737662296980) 932308482793999221) 492790837847079868) 24482313207330744) 557589630170283256) 444351093178823510) 93713807124957186) 168511850375400535) 250801719802533920) 165637734320622731) 711015059039157782) 879868234931579289) 250393095354819156) 420226237574000944) 931142531056943066) 361730178877598106) 343509334351342708) 670504428239226600) 28766920860737226) 696662931017434962) 574263072709985323) 773861066969186320)
|6,4=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 18 529761083407855296) 477175019081840615) 893892686145388554) 986222393935073751) 457712151484320678) 379567948250870454) 236246700280758684) 917132677097768504) 842544966097177737) 826329783345674182) 924043811095298546) 73258737851054183) 382439674386750791) 721934932927060793) 596449935766112407) 499640061070797377) 763838938955680951) 49122215091528992) 335972446408531618) 820620998489637065) 695660395530928672) 438488556119393994) 338747077919245025) 225480703648959801) 83165638312992463) 850414896880413246) 192488509645760408) 97400725913443375) 936835637362749876) 114980402668342975) 18121811837868203) 615273531877538391) 610689723767191074) 594750773029354371) 633617985452118045) 163135646761989013) 212401120825076901) 806112011747488039) 421663994800024757) 567159792155230208)
|6,5=>(pn (pn (pn (pn (pn (pn (pn (pn 24 973992310014694172) 839663920041736407) 365484194156381849) 2635583036143780) 727939324291804171) 686986404206315664) 644515715001672976) 179264620970639360)
|7,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 636690795051 460627774993731603) 158843713972915040) 100418749087429636) 926444415780462273) 213100256904566105) 710512519563613199) 858645191058341745) 806433260154498966) 337535167385982935) 646725560141727265) 455111856209603859) 888018692766094614) 231247292837748329) 477832404059580815) 962075454474339822) 15187749953309159) 718324074451304831) 416459339653361180) 438201824778105856) 834281135044520110) 996675019061211213) 642405874995664551) 413576287984376637) 794434417159824936) 455600151837159573) 287694098321818949) 282057602467223233) 366011180693470851) 795388800617215740) 725809105849993301) 593236080988127435) 971523530906408157) 736765126251028911) 175155812827407553) 3505844044348682) 822498695060209340) 397347533847999639) 84511582669586068) 386152623231017836) 431679392170901536)
|7,1=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 170314859 806863516863142389) 564855201069423377) 258412727080807638) 52918544937917499) 877590377731245589) 831189644137096208) 142544765735537932) 701928992713711484) 659045906599280649) 136036980935730465) 72155661033612798) 823410543701278765) 292004152392438990) 576715315709368674) 878832005520734761) 740998729847774073) 406914794613707373) 207755386110784621) 164381287479489787) 880530546136454484) 517181097721778041) 253511040339501396) 927355709492868551) 133663663546001063) 101218538850152431) 606065979433737335) 304611071039470914) 648239766964705088) 979552865269830378) 603517915082776793) 713894451533707439) 603778081104386133) 876298950891473651) 166688296131794100) 144392006531536460) 586511337218443223) 786634581275265387) 174211840397071970) 787261498861005863) 43758012917874817)
|7,2=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 26 420322422254064157) 782924495234635906) 397929333323710183) 342031416935571314) 535797666253607357) 905541386985659944) 340659109847804715) 982810364365382403) 217393278497238740) 944613302541182590) 188596639014918127) 439308564709626468) 908398309547113678) 6202532447470620) 45172720437598421) 763727279072775976) 283697593532247633) 708108572124650247) 840085881842896552) 470248102011742680) 629857016847325355) 970231522523751763) 43672427499880469)
|8,0=>(pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn (pn 1308108666 599092359334374682) 242329690179797262) 173924889033346068) 635183044665941862) 674267129188675830) 432416353347147833) 928112315057765742) 637814500532787034) 171015537142519227) 968984059288805893) 978242599348909918) 306604413324522141) 230946767651644039) 113121426189651578) 687773052755120906) 877412852502364189)
|9,0=>(pn (pn 86 223286366714400128) 382491096891523103)
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

def symsG : List (List (Nat × Nat)) := [[((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14), ((pn (pn (pn 26855044144683 368651945175119862) 498915403158948544) 192291250173443840), 24)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 300 368584273193762447) 654954626946583276) 964940766901592839) 59880694975692970), 7), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)], [((pn (pn (pn 17973297773915 692040494557306782) 974534527635025457) 962028258579622570), 31), ((pn (pn (pn (pn 1 413456084194469633) 14278773928472866) 970047266925743491) 944490397887155404), 14)]]
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

end PEqualNP.Outside.L_meta_32169_aux.NatCore

namespace PEqualNP.Outside.L_meta_32169_aux.ReuseEight

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 8 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 8) : BF := fun x => x i

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_self (k : Fin 4) (a : ℕ) : gN k a a = 0 ∨ gN k a a = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_lt (k : Fin 4) (a b : ℕ) (ha : a < 1024) (hb : b < 1024) : gN k a b < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  have hp : (1024 : ℕ) ≤ 2 ^ i :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi)
  rw [gN_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]
  fin_cases k <;> rfl

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gate {ρ : Type} (k : Fin 4) (a b : ρ → Bool) (l : List ρ) :
    enc (fun r => zeroGate k (a r) (b r)) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 8 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

def zF : BF := fun _ => false

def rst (p : Fin 8) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 8 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 8} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 8} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 8) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 8} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 8} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 8 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 8) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 8) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 8) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 8) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 8) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 8 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 8 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def graphTable (a : ℕ) (x : Fin 8 → Bool) : Bool := a.testBit (tableIndex x)

def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

theorem inputVector (x : Fin 8 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  funext i
  fin_cases i <;> rfl

theorem equalEight {f g : (Fin 8 → Bool) → Bool}
    (h : ∀ a b c d e v w z : Bool, f ![a, b, c, d, e, v, w, z] = g ![a, b, c, d, e, v, w, z]) : f = g := by
  funext x
  rw [inputVector x]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [if_neg (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 8)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩

end PEqualNP.Outside.L_meta_32169_aux.ReuseEight

namespace PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction

def gate (k : Fin 4) (a b : Bool) : Bool :=
  if k = 0 then a && b else if k = 1 then a || b
  else if k = 2 then a && !b else !a && b

def phaseKind (k : Fin 4) (a b : Bool) : Fin 4 :=
  if k = 0 then
    if a then (if b then 1 else 3) else (if b then 2 else 0)
  else if k = 1 then
    if a then (if b then 0 else 2) else (if b then 3 else 1)
  else if k = 2 then
    if a then (if b then 3 else 1) else (if b then 0 else 2)
  else
    if a then (if b then 2 else 0) else (if b then 1 else 3)

theorem phase_identity (k : Fin 4) (a b x y : Bool) :
    xor (gate k x y) (gate k a b) =
      gate (phaseKind k a b) (xor x a) (xor y b) := by
  fin_cases k <;> cases a <;> cases b <;> cases x <;> cases y <;> decide

def normalizedRestriction {ι : Type*} [DecidableEq ι]
    (p : ι) (b : Bool) (f : (ι → Bool) → Bool) (x : ι → Bool) : Bool :=
  xor (f (Function.update x p b)) (f (Function.update (fun _ => false) p b))

theorem restrict_gate {ι : Type*} [DecidableEq ι]
    (p : ι) (b : Bool) (k : Fin 4) (f g : (ι → Bool) → Bool) :
    normalizedRestriction p b (fun x => gate k (f x) (g x)) =
      fun x => gate
        (phaseKind k (f (Function.update (fun _ => false) p b))
          (g (Function.update (fun _ => false) p b)))
        (normalizedRestriction p b f x) (normalizedRestriction p b g x) := by
  funext x
  exact phase_identity _ _ _ _ _

theorem restrict_self {ι : Type*} [DecidableEq ι] (p : ι) (b : Bool) :
    normalizedRestriction p b (fun x => x p) = fun _ => false := by
  funext x
  simp [normalizedRestriction]

theorem restrict_other {ι : Type*} [DecidableEq ι] (p q : ι) (b : Bool)
    (h : q ≠ p) : normalizedRestriction p b (fun x => x q) = fun x => x q := by
  funext x
  simp [normalizedRestriction, Function.update_of_ne h]

end PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction

namespace PEqualNP.Outside.L_meta_32169_aux.ZeroGateTwo
open PEqualNP.Outside.L_meta_32169_aux.ReuseEight

def deaths (ρ : BF → BF) (ws : List BF) : ℕ :=
  ws.countP fun w => decide (ρ w = zF)

theorem deaths_cons (ρ : BF → BF) (a : BF) (r : List BF) :
    deaths ρ (a :: r) = deaths ρ r + if ρ a = zF then 1 else 0 := by
  simp [deaths, List.countP_cons]

theorem deaths_rep (ρ : BF → BF) (n : ℕ) (g : BF) (r : List BF) :
    deaths ρ (List.replicate n g ++ r) = (if ρ g = zF then n else 0) + deaths ρ r := by
  simp only [deaths, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

def Good (ρ : BF → BF) (F : BF) (s : ℕ) (ws : List BF) (cap : ℕ) : Prop :=
  max (deaths ρ ws) cap ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, ρ w ≠ zF → S (ρ w)) →
    UC gF (fun _ => True) (s - max (deaths ρ ws) cap) S (ρ F)

theorem good_perm {ρ : BF → BF} {F : BF} {s cap : ℕ} {xs ys : List BF}
    (hp : xs.Perm ys) (h : Good ρ F s xs cap) : Good ρ F s ys cap := by
  have hc : deaths ρ ys = deaths ρ xs := (hp.countP_eq _).symm
  unfold Good at h ⊢
  rw [hc]
  exact ⟨h.1, fun S hS => h.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩

theorem good_step (ρ : BF → BF)
    (hr : ∀ k a b, ∃ k', ρ (gF k a b) = gF k' (ρ a) (ρ b))
    {F : BF} {s cap : ℕ} {a b : BF} {r : List BF} (k : Fin 4) (u : ℕ)
    (ih : Good ρ F s (List.replicate (u+1) (gF k a b) ++ r) cap) :
    Good ρ F (s+1) (a :: b :: r) cap := by
  obtain ⟨k', hg⟩ := hr k a b
  obtain ⟨ih1, ih2⟩ := ih
  unfold Good
  rw [deaths_rep] at ih1 ih2
  rw [deaths_cons, deaths_cons]
  have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, ρ w ≠ zF → S (ρ w)) →
      ∀ w ∈ r, ρ w ≠ zF → S (ρ w) := fun S hS w hw => hS w (by simp [hw])
  by_cases ha : ρ a = zF <;> by_cases hb : ρ b = zF
  · have hgz : ρ (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
    simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
    refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
    intro w hw hwz
    rcases List.mem_append.1 hw with hw | hw
    · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
    · exact hmem S hS w hw hwz
  · by_cases hgz : ρ (gF k a b) = zF
    · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · have hgb : ρ (gF k a b) = ρ b := by
        rcases gF_zero_left k' (ρ b) with h | h
        · exact absurd (by rw [hg, ha, h]) hgz
        · rw [hg, ha, h]
      simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw, hgb]
        exact hS b (by simp) hb
      · exact hmem S hS w hw hwz
  · by_cases hgz : ρ (gF k a b) = zF
    · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · have hga : ρ (gF k a b) = ρ a := by
        rcases gF_zero_right k' (ρ a) with h | h
        · exact absurd (by rw [hg, hb, h]) hgz
        · rw [hg, hb, h]
      simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw, hga]
        exact hS a (by simp) ha
      · exact hmem S hS w hw hwz
  · by_cases hgz : ρ (gF k a b) = zF
    · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => ?_⟩
      have h1 := ih2 (fun w => w = gF k' (ρ a) (ρ b) ∨ S w) (by
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
        · exact Or.inr (hmem S hS w hw hwz))
      have h2 := UC_gate k' (ρ a) (ρ b) trivial (hS a (by simp) ha) (hS b (by simp) hb) h1
      exact UC_le (by omega) h2

theorem good_birth (ρ : BF → BF) {F : BF} {s : ℕ} {a b : BF} {r : List BF}
    (k : Fin 4) (u : ℕ) (hgz : ρ (gF k a b) = zF)
    (ih : Good ρ F s (List.replicate (u+1) (gF k a b) ++ r) 0) :
    Good ρ F (s+1) (a :: b :: r) 2 := by
  obtain ⟨ih1, ih2⟩ := ih
  unfold Good
  rw [deaths_rep] at ih1 ih2
  rw [deaths_cons, deaths_cons]
  simp only [hgz, ite_true, Nat.max_zero] at ih1 ih2
  split_ifs <;> refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
  all_goals
    intro w hw hwz
    rcases List.mem_append.1 hw with hw | hw
    · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
    · exact hS w (by simp [hw]) hwz

def ρ (p : Fin 8) (bit : Bool) : BF → BF :=
  PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.normalizedRestriction p bit

theorem phase_gate_eq (k : Fin 4) (a b : Bool) :
    PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.gate k a b = zeroGate k a b := by
  fin_cases k <;> rfl

theorem rho_gate (p : Fin 8) (bit : Bool) (k : Fin 4) (a b : BF) :
    ∃ k', ρ p bit (gF k a b) = gF k' (ρ p bit a) (ρ p bit b) := by
  refine ⟨PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.phaseKind k
    (a (Function.update (fun _ => false) p bit))
    (b (Function.update (fun _ => false) p bit)), ?_⟩
  funext x
  simpa only [ρ, PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.normalizedRestriction, gF, phase_gate_eq] using PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.phase_identity k
    (a (Function.update (fun _ => false) p bit))
    (b (Function.update (fun _ => false) p bit))
    (a (Function.update x p bit)) (b (Function.update x p bit))

theorem rho_self (p : Fin 8) (bit : Bool) : ρ p bit (var p) = zF :=
  PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.restrict_self p bit

theorem rho_other {i p : Fin 8} (bit : Bool) (h : i ≠ p) :
    ρ p bit (var i) = var i := PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.restrict_other p i bit h

theorem canal_left (p : Fin 8) (k : Fin 4) (b : BF) :
    ∃ bit, ρ p bit (gF k (var p) b) = zF := by
  obtain ⟨bit, c, hc⟩ := (zeroGate_canalizes k).2
  refine ⟨bit, funext fun x => ?_⟩
  simp [ρ, PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.normalizedRestriction, gF, var, hc, zF]

theorem canal_right (p : Fin 8) (k : Fin 4) (a : BF) :
    ∃ bit, ρ p bit (gF k a (var p)) = zF := by
  obtain ⟨bit, c, hc⟩ := (zeroGate_canalizes k).1
  refine ⟨bit, funext fun x => ?_⟩
  simp [ρ, PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.normalizedRestriction, gF, var, hc, zF]

theorem tr_cap_two (p : Fin 8) {F : BF} (hn : ∀ bit, ρ p bit F ≠ zF)
    {s : ℕ} {ws : List BF} (h : TR gF (fun _ _ _ => True) [F] s ws) :
    (∀ bit, Good (ρ p bit) F s ws 0) ∧
      (var p ∈ ws → ∃ bit, Good (ρ p bit) F s ws 2) := by
  refine TR.ind (P := fun s ws =>
    (∀ bit, Good (ρ p bit) F s ws 0) ∧
      (var p ∈ ws → ∃ bit, Good (ρ p bit) F s ws 2)) h ?_ ?_ ?_
  · constructor
    · intro bit
      have hd : deaths (ρ p bit) [F] = 0 := by simp [deaths, hn bit]
      unfold Good
      rw [hd]
      refine ⟨by omega, fun S hS => ?_⟩
      exact hS F (by simp) (hn bit)
    · intro hp
      have he : var p = F := List.mem_singleton.1 hp
      exact False.elim (hn false (by rw [← he, rho_self]))
  · intro s xs ys hp _ ih
    exact ⟨fun bit => good_perm hp (ih.1 bit), fun hmem => by
      obtain ⟨bit, hb⟩ := ih.2 (hp.mem_iff.2 hmem)
      exact ⟨bit, good_perm hp hb⟩⟩
  · intro s a b r k u _ _ ih
    constructor
    · intro bit
      exact good_step (ρ p bit) (rho_gate p bit) k u (ih.1 bit)
    · intro hp
      by_cases hold : var p ∈ List.replicate (u+1) (gF k a b) ++ r
      · obtain ⟨bit, hb⟩ := ih.2 hold
        exact ⟨bit, good_step (ρ p bit) (rho_gate p bit) k u hb⟩
      · rcases List.mem_cons.1 hp with ha | hp
        · subst a
          obtain ⟨bit, hb⟩ := canal_left p k b
          exact ⟨bit, good_birth (ρ p bit) k u hb (ih.1 bit)⟩
        · rcases List.mem_cons.1 hp with hb | hp
          · subst b
            obtain ⟨bit, hb⟩ := canal_right p k a
            exact ⟨bit, good_birth (ρ p bit) k u hb (ih.1 bit)⟩
          · exact False.elim (hold (List.mem_append.2 (Or.inr hp)))

theorem rho_zero (p : Fin 8) (bit : Bool) : ρ p bit zF = zF := by
  funext x
  simp [ρ, PEqualNP.Outside.L_meta_32169_aux.PhaseRestriction.normalizedRestriction, zF]

theorem remove_var_two (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : ∀ bit, ρ p bit F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ bit t, t + 2 ≤ s ∧
      UC gF (fun _ => True) t (sourceVars (xs.erase p)) (ρ p bit F) := by
  have hf : F ≠ zF := fun he => hn false (by rw [he, rho_zero])
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun he => hmiss (he ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  obtain ⟨bit, hb⟩ := (tr_cap_two p hn (TR.monoC (fun _ _ _ _ => trivial) run)).2 hp
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨bit, k - max (deaths (ρ p bit) ws) 2, by omega, hb2 _ ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun he => hz (he ▸ rho_self p bit)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rho_other bit hne⟩

end PEqualNP.Outside.L_meta_32169_aux.ZeroGateTwo

namespace PEqualNP.Outside.L_meta_32169_aux.NatDomainBridge
open PEqualNP.Outside.L_meta_32169_aux.ReuseEight
open PEqualNP.Outside.L_meta_32169_aux.NatCore

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def sample (rows : Fin 256 → Fin 8 → Bool) (f : BF) : Nat :=
  enc f (List.ofFn rows)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sample_gate (rows : Fin 256 → Fin 8 → Bool) (d : Nat)
    (hd : d &&& mask256 = d) (k : Fin 4) (a b : BF) :
    sample rows (gF k a b) &&& d = opD d k.val (sample rows a) (sample rows b) &&& d := by
  change enc (gF k a b) (List.ofFn rows) &&& d = _
  rw [enc_gF]
  change gN k (sample rows a) (sample rows b) &&& d = _
  apply Nat.eq_of_testBit_eq
  intro i
  have hm := congrArg (fun v => v.testBit i) hd
  simp only [Nat.testBit_and] at hm
  simp only [Nat.testBit_and, gN_testBit]
  fin_cases k <;> simp only [opD, andD, orD, negD, zeroGate, Nat.testBit_and,
    Nat.testBit_or, Nat.testBit_xor] <;>
    cases hdv : d.testBit i <;> cases hmv : mask256.testBit i <;>
    cases hav : (sample rows a).testBit i <;> cases hbv : (sample rows b).testBit i <;> simp_all

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uc_reach (rows : Fin 256 → Fin 8 → Bool) (d : Nat)
    (hd : d &&& mask256 = d) (roots : List Nat) :
    ∀ s S F, UC gF (fun _ => True) s S F →
      ∀ p bank, NatReach true d roots p bank →
        (∀ f, S f → Avail true d bank (sample rows f)) →
        ∃ q next, q ≤ p+s ∧ NatReach true d roots q next ∧ Avail true d next (sample rows F)
  | 0, S, F, h, p, bank, hr, hs => ⟨p, bank, by omega, hr, hs F h⟩
  | s+1, S, F, h, p, bank, hr, hs => by
    rcases h with h | ⟨k, a, b, _, ha, hb, h⟩
    · obtain ⟨q, next, hq, hn, hf⟩ := uc_reach rows d hd roots s S F h p bank hr hs
      exact ⟨q, next, by omega, hn, hf⟩
    · have hop : allowedB true k.val = true := by simp [allowedB, k.isLt]
      let z := opD d k.val (sample rows a) (sample rows b)
      have hn : NatReach true d roots (p+1) (z :: bank) :=
        ⟨bank, sample rows a, sample rows b, k.val, hop, rfl, hr, hs a ha, hs b hb⟩
      have hsrc : ∀ f, (f = gF k a b ∨ S f) → Avail true d (z :: bank) (sample rows f) := by
        intro f hf
        rcases hf with rfl | hf
        · exact Or.inr (Or.inl ⟨z, List.mem_cons_self, (sample_gate rows d hd k a b).symm⟩)
        · exact avail_cons z _ (hs f hf)
      obtain ⟨q, next, hq, hn, hf⟩ := uc_reach rows d hd roots s _ F h (p+1) _ hn hsrc
      exact ⟨q, next, by omega, hn, hf⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lower_uc (rows : Fin 256 → Fin 8 → Bool) (d : Nat)
    (hd : d &&& mask256 = d) (roots : List Nat) (T L : Nat)
    (lower : Lower true d roots T L) (S : BF → Prop) (F : BF)
    (target : sample rows F &&& d = T &&& d)
    (source : ∀ f, S f → Avail true d roots (sample rows f))
    (s : Nat) (h : UC gF (fun _ => True) s S F) : L ≤ s := by
  obtain ⟨q, next, hq, hr, hf⟩ := uc_reach rows d hd roots s S F h 0 roots rfl source
  have hl := lower q next hr (avail_of_eq target hf)
  omega
end PEqualNP.Outside.L_meta_32169_aux.NatDomainBridge

namespace PEqualNP.Outside.L_meta_32169_aux
open PEqualNP.Outside.L_meta_32169_aux.ReuseEight PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_32169_aux.ZeroGateTwo
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def coreGraph (x : Fin 8 → Bool) : Bool := (x 1 && x 4) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 7) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def coreSources : Finset (Fin 8) := (Finset.univ.erase 3).erase 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem restrictedCore (b : Bool) : rst 0 (ρ 3 b graph) = coreGraph := by
  cases b <;> exact equalEight (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lower_with_not
    (coreBound : ∀ t, UC gF (fun _ => True) t (sourceVars coreSources) coreGraph → 11 ≤ t)
    (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = graph x) :
    15 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = graph := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (by decide : graph (fun _ => false) = false)] at start
  rcases start with e | base
  · have c := congrFun e (assignment 9)
    exact False.elim ((by decide : graph (assignment 9) ≠ false) c)
  have hn : ∀ b, ρ 3 b graph ≠ zF := by
    intro b e
    have c := congrFun e (assignment 18)
    cases b <;> exact (by decide : _ ≠ false) c
  obtain ⟨b,t,pay,h⟩ := remove_var_two graph 3 Finset.univ (countBinary gates)
    ⟨assignment 9,by decide⟩ hn base
  have hd : ∃ x, rst 0 (ρ 3 b graph) x ≠ ρ 3 b graph x := by
    cases b
    · exact ⟨assignment 33,by decide⟩
    · exact ⟨assignment 1,by decide⟩
  have nz : rst 0 (ρ 3 b graph) ≠ zF := by
    rw [restrictedCore]
    intro e
    have c := congrFun e (assignment 18)
    exact (by decide : coreGraph (assignment 18) ≠ false) c
  obtain ⟨u,pay2,hu⟩ := remove_var (ρ 3 b graph) 0 (Finset.univ.erase 3) t hd nz h
  rw [restrictedCore] at hu
  have lo := coreBound u hu
  have extra := countBinary_lt gates hnot
  omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def witness : Circuit := ⟨[⟨.or,[5, 7]⟩, ⟨.and,[2, 8]⟩, ⟨.and,[1, 4]⟩, ⟨.or,[0, 7]⟩, ⟨.or,[5, 6]⟩, ⟨.and,[11, 12]⟩, ⟨.and,[0, 3]⟩, ⟨.or,[0, 1]⟩, ⟨.or,[15, 4]⟩, ⟨.or,[6, 7]⟩, ⟨.and,[16, 17]⟩, ⟨.or,[9, 10]⟩, ⟨.or,[19, 13]⟩, ⟨.or,[20, 14]⟩, ⟨.or,[21, 18]⟩],22⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = graph x := by decide +kernel
end PEqualNP.Outside.L_meta_32169_aux

namespace PEqualNP.Outside.L_meta_32169_aux
open PEqualNP.Outside.L_meta_32169_aux.ReuseEight PEqualNP.CircuitLowerBounds

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def coreRows (r : Fin 256) : Fin 8 → Bool :=
  ![false, r.val.testBit 0, r.val.testBit 1, false, r.val.testBit 3,
    r.val.testBit 4, r.val.testBit 5, r.val.testBit 7]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coreDomain : NatCore.dom_187 &&& NatCore.mask256 = NatCore.dom_187 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coreTarget : PEqualNP.Outside.L_meta_32169_aux.NatDomainBridge.sample coreRows coreGraph &&& NatCore.dom_187 =
    NatCore.goal_187 &&& NatCore.dom_187 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coreSourcesGood : ∀ i ∈ coreSources, ∃ v ∈ NatCore.roots_187,
    v &&& NatCore.dom_187 = PEqualNP.Outside.L_meta_32169_aux.NatDomainBridge.sample coreRows (var i) &&& NatCore.dom_187 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coreLower (t : Nat)
    (h : UC gF (fun _ => True) t (sourceVars coreSources) coreGraph) : 11 ≤ t :=
  PEqualNP.Outside.L_meta_32169_aux.NatDomainBridge.lower_uc coreRows NatCore.dom_187 coreDomain NatCore.roots_187 NatCore.goal_187 11
    NatCore.low_187 (sourceVars coreSources) coreGraph coreTarget
    (fun f hf => by
      obtain ⟨i, hi, rfl⟩ := hf
      exact Or.inr (Or.inl (coreSourcesGood i hi))) t h
end PEqualNP.Outside.L_meta_32169_aux
open PEqualNP.Outside.L_meta_32169_aux PEqualNP.Outside.L_meta_32169_aux.ReuseEight PEqualNP.CircuitLowerBounds in

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_32169 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · have lo := lower_with_not coreLower gs o legal neg computes
    exact ⟨witness.gates,witness.output,by simp [witness],lo,witnessCorrect⟩
  · refine ⟨gs,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨op,cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g,hg,eq⟩)),cap⟩
