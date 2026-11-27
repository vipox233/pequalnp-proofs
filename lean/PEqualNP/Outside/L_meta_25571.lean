import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25545

namespace PEqualNP.Outside.L_meta_25571_aux
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Scan (summary)
variable {k : Nat} (P : Params k)
def width := if P.a=P.r-5 then (summary P.v P.a).2-P.d else 0
def pivotBit (cell : Nat) := (List.range P.a).any (fun j => (List.range 3).any (fun s => (left P.q P.v j+s) % k == cell)) || (List.range (width P)).any (fun j => (P.q+j) % k == cell)
lemma sep {n : Nat} (hn : n<P.N) : P.q-k+width P ≤ P.pp n := by
  have base:=(P.interval hn).1
  by_cases h:P.a=P.r-5
  · rw [width, if_pos h]
    have hr:=P.hr; have hkd:=P.hkd;have hd:=P.hd
    have ja:n/3<P.a := by dsimp [Params.N] at hn;omega
    have bounds:= summaryMono P.v (i:=n/3) (j:=P.a) (by omega)
    have big:=P.big (j:=n/3) (by omega)
    dsimp only [Params.pp,left,edge,tick,Params.q] at *; omega
  · simpa only [width,h,ite_false,Nat.add_zero] using base
lemma width_le : width P ≤ k := by
  have H:=P.him
  have G:=(summaryMono P.v (i:=0) (j:=P.a) (by omega)).2
  change (summary P.v P.a).2 ≤ 0 + 2*(P.a-0) at G
  unfold width; split <;> omega
lemma qge : k ≤ P.q := by have:=P.hr;have:=P.hd;dsimp [Params.q];omega
lemma shifted (b : Nat) : (P.q+b) % k = (P.q-k+b) % k := by
  conv_lhs => rw [show P.q+b=(P.q-k+b)+k by have:=qge P;omega,Nat.add_mod_right]
def outPv (j : Fin (width P)) : Fin k := ⟨(P.q+j.val)%k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
lemma outInj : Function.Injective (outPv P) := by
  intro x y h
  have hm := congrArg Fin.val h
  change (P.q+x.val)%k=(P.q+y.val)%k at hm
  rw [shifted,shifted] at hm
  have hq:=qge P; have hw:=width_le P
  have hx:=x.isLt; have hy:=y.isLt
  have e:=P.sameMod (x:=P.q-k+x.val) (y:=P.q-k+y.val) (by omega) (by omega) (by omega) (by omega) hm
  exact Fin.ext (by omega)
lemma outNotTranscript (n : Fin P.N) (j : Fin (width P)) : P.pv n.val ≠ outPv P j := by
  intro h
  have hm:= congrArg Fin.val h
  change (P.pp n.val)%k=(P.q+j.val)%k at hm
  rw [shifted] at hm
  have hq:=qge P; have hw:=width_le P; have hj:=j.isLt
  have e:=P.sameMod (P.interval n.isLt).1 (P.interval n.isLt).2 (by omega : P.q-k ≤ P.q-k+j.val) (by omega) hm
  have := sep P n.isLt;omega
lemma pivotSpec (b : Fin k) : pivotBit P b.val = true ↔ (∃ n : Fin P.N, P.pv n.val=b) ∨ (∃ j : Fin (width P), outPv P j=b) := by
  simp only [pivotBit,Bool.or_eq_true,List.any_eq_true,List.mem_range,beq_iff_eq]
  constructor
  · rintro (⟨j,hj,s,hs,e⟩|⟨j,hj,e⟩)
    · let n:=3*j+(2-s)
      have hn:n<P.N := by dsimp [n,Params.N];omega
      left; refine ⟨⟨n,hn⟩,Fin.ext ?_⟩
      dsimp only [Params.pv,Params.pp]
      rw [show n/3=j by dsimp [n];omega,show n%3=2-s by dsimp [n];omega,
        show left P.q P.v j+2-(2-s)=left P.q P.v j+s by omega];exact e
    · exact Or.inr ⟨⟨j,hj⟩,Fin.ext e⟩
  · rintro (⟨n,e⟩|⟨j,e⟩)
    · left; have hn:=n.isLt;change n.val<3*P.a at hn
      have h:=congrArg Fin.val e
      refine ⟨n.val / 3,by omega,2-n.val % 3,by omega,?_⟩
      change (left P.q P.v (n.val / 3)+2-n.val % 3)%k = _ at h
      rwa [show left P.q P.v (n.val / 3)+(2-n.val % 3)=left P.q P.v (n.val / 3)+2-n.val % 3 by omega]
    · exact Or.inr ⟨j.val,j.isLt,congrArg Fin.val e⟩
lemma freeCard : ((List.range k).filter (fun b => !(pivotBit P b))).length = k-3*P.a-width P := by
  classical
  let T := (Finset.univ : Finset (Fin P.N)).image (fun n => P.pv n.val)
  let O := (Finset.univ : Finset (Fin (width P))).image (outPv P)
  have ti : Function.Injective (fun (n : Fin P.N) => P.pv n.val) := fun x y e => Fin.ext (P.distinct _ x.isLt _ y.isLt e)
  have ct:T.card=P.N := by simp [T,Finset.card_image_of_injective _ ti]
  have co:O.card=width P := by simp [O,Finset.card_image_of_injective _ (outInj P)]
  have dis:Disjoint T O := by
    rw [Finset.disjoint_left]; intro b ht ho
    obtain ⟨n,_,rfl⟩:=Finset.mem_image.mp ht
    obtain ⟨j,_,e⟩:=Finset.mem_image.mp ho
    exact outNotTranscript P n j e.symm
  rw [length_filter_range_eq_card_fin]
  have F : ((Finset.univ : Finset (Fin k)).filter (fun b => (!(pivotBit P b.val)) = true)) = (T ∪ O)ᶜ := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,Finset.mem_union, T,O,Finset.mem_image,exists_const,Bool.not_eq_true']
    have h:=pivotSpec P b
    cases z:pivotBit P b.val <;> simp_all
  rw [F,Finset.card_compl,Finset.card_union_of_disjoint dis,ct,co,Fintype.card_fin]; dsimp [Params.N];omega
end PEqualNP.Outside.L_meta_25571_aux

namespace PEqualNP.Outside.L_meta_25571_aux.Semantics
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep lInj lGuard cut gPivot lineStep_agree_interval lineStep_xor_pivot stateAt)
open PEqualNP.Outside.L_meta_25545_aux.Word (par src word39)
open PEqualNP.Outside.L_meta_25545_aux.Word.Layout (inputWord)
open PEqualNP.Outside.L_meta_25545_aux.Scan (summary scan_gain_le)
open PEqualNP.Outside.L_meta_25545_aux.Word.Solver
variable {k : Nat} (P : Params k)
theorem intervalTri (u : Fin (2^k)) (c : Nat→Fin (2^k)) :
    ∀ n<P.N, ∀ x y, Good (P.err u c) n x → Good (P.err u c) n y →
      (∀ j, P.pp n<j → j<P.q → x.val.testBit (j%k)=y.val.testBit (j%k)) →
      xor (P.err u c n x) (x.val.testBit (P.pv n).val)=xor (P.err u c n y) (y.val.testBit (P.pv n).val) := by
  intro n hn x y gx gy same
  let j:=n/3
  let t:=tick j
  let e:=edge P.q P.v j
  let mode:=(summary P.v j).1
  let f:=cut P.q (word39 u (inputWord u x))
  let g:=cut P.q (word39 u (inputWord u y))
  have jl:j<P.a := by dsimp [j];dsimp [Params.N] at hn;omega
  have big:=P.big (j:=j) (by omega)
  have ht:5≤t := by dsimp [t,tick];omega
  have he:2*t+5≤e := by dsimp [e,edge,t,tick];omega
  have rawX:=cutQueries45 u c (inputWord u x) (by have:=P.kLarge;omega) big
    (P.earlierPrefix (j:=j) (by dsimp [j];omega) gx)
  have rawY:=cutQueries45 u c (inputWord u y) (by have:=P.kLarge;omega) big
    (P.earlierPrefix (j:=j) (by dsimp [j];omega) gy)
  have a (n' : Nat) (h:P.pp n<n') : f n'=g n' := by
    by_cases hr:n'<P.q
    · simpa only [f,g,cut,ite_eq_left hr,word39,P.srcRecover] using same n' h hr
    · simp [f,g,cut,hr]
  have right : xor (f (P.pp n)) (g (P.pp n))=xor (x.val.testBit (P.pv n).val) (y.val.testBit (P.pv n).val) := by
    simp only [f,g,cut,ite_eq_left (P.interval hn).2,word39,P.srcRecover,Params.pv]
  suffices h : xor (P.obs u c (inputWord u x).val n) (P.obs u c (inputWord u y).val n) =
      xor (f (P.pp n)) (g (P.pp n)) by
    exact (show ∀ a b c d e:Bool, xor a b=xor c d → xor (xor a e) c=xor (xor b e) d by decide) _ _ _ _ _ (h.trans right)
  by_cases z:n % 3=0
  · have which : P.pp n=e+3-2*t+2 := by simp only [Params.pp,z,Nat.sub_zero];rfl
    simp only [Params.obs,z,ite_true,which]
    rw [rawX.1,rawY.1]
    exact onePivot u c f g mode t e ht he (fun n' hh=>a n' (by rwa [which]))
  · by_cases o:n % 3=1
    · have which : P.pp n=e+3-2*t+1 := by unfold Params.pp;rw [o];change e+3-2*t+2-1=_;omega
      simp only [Params.obs,z,o,ite_false,ite_true,which]
      rw [rawX.2.1,rawY.2.1]
      exact twoPivot u c f g mode t e ht he (fun n' hh=>a n' (by rwa [which]))
    · have r:n % 3=2 := by omega
      have which :P.pp n=e+1-2*(t-1) := by unfold Params.pp;rw [r];change e+3-2*t+2-2=_;omega
      simp only [Params.obs,z,o,ite_false,which]
      rw [rawX.2.2,rawY.2.2]
      exact gPivot u c f g (s:=t-1) (e:=e) (by omega) (by omega) (fun n' hh=>a n' (by rwa [which]))

abbrev M := if P.a=P.r-5 then (summary P.v P.a).2-P.d else 0
abbrev L := P.N+M P
def outIdx (n : Nat) := L P - 1 - n
def pos (n : Nat) := if n<P.N then P.pp n else P.q-k+outIdx P n
def pv (n : Nat) : Fin k := ⟨pos P n % k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
lemma mLe : M P ≤ k := by
  have := P.him
  have := P.ha
  have g := scan_gain_le P.v P.a 0
  change (summary P.v P.a).2≤2*P.a at g
  unfold M; split <;> omega
lemma qLe : k ≤ P.q := by have:=P.hd; dsimp [Params.q];omega
lemma low {n : Nat} (hn:n<P.N) : P.q-k+M P ≤ P.pp n := by
  by_cases done : P.a=P.r-5
  · have g:=summaryMono P.v (i:=n/3) (j:=P.a) (by dsimp [Params.N] at hn;omega)
    have big:=P.big (j:=n/3) (by dsimp [Params.N] at hn;omega)
    have:=P.hkd;have:=P.hr;have:=P.hd;have:=P.eligible
    have I:=(P.interval hn).1
    rw [show M P=(summary P.v P.a).2-P.d by simp [M,done]]
    have := Nat.mod_lt n (by decide : 0<3)
    dsimp only [Params.pp,left,edge,tick,Params.q,Params.N] at *
    omega
  · simpa [M,done] using (P.interval hn).1
lemma inWindow {n : Nat} (hn:n<L P) : P.q-k ≤ pos P n ∧ pos P n < P.q := by
  unfold pos
  split
  · next h => exact P.interval h
  · next h => have:=mLe P;have:=qLe P;dsimp [outIdx,L] at *;omega
lemma desc {n t : Nat} (nt:n<t) (ht:t<L P) : pos P t < pos P n := by
  unfold pos
  by_cases h:t<P.N
  · simp [h,show n<P.N by omega,P.decreasing nt h]
  · rw [if_neg h]
    split
    · next hn => have:=low P hn;dsimp [outIdx,L] at *;omega
    · dsimp [outIdx,L] at *;omega
lemma distinct {n t : Nat} (hn:n<L P) (ht:t<L P) (eq:pv P n=pv P t) : n=t := by
  have same:=P.sameMod (inWindow P hn).1 (inWindow P hn).2 (inWindow P ht).1 (inWindow P ht).2 (congrArg Fin.val eq)
  rcases lt_trichotomy n t with h|h|h
  · have:=desc P h ht;omega
  · exact h
  · have:=desc P h hn;omega
lemma past {t : Nat} (ht:t<L P) {x y : Fin (2^k)}
    (same:∀ b:Fin k, ¬Future (pv P) t (L P) b.val → x.val.testBit b.val=y.val.testBit b.val)
    (j : Nat) (lo:pos P t<j) (hr:j<P.q) : x.val.testBit (j % k)=y.val.testBit (j % k) := by
  apply same ⟨j % k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
  rintro ⟨z,hz,hl,eq⟩
  have low': P.q-k ≤ j := by have := (inWindow P ht).1;omega
  have e:=P.sameMod (inWindow P hl).1 (inWindow P hl).2 low' hr eq
  by_cases ez:t=z
  · subst z;omega
  · have := desc P (by omega : t<z) hl;omega

lemma pvIn {n : Nat} (h:n<P.N) : pv P n=P.pv n := by apply Fin.ext; simp [pv,pos,h,Params.pv]
lemma pvOut {n : Nat} (h:P.N≤n) : (pv P n).val=(P.q+outIdx P n)%k := by
  simp [pv,pos,Nat.not_lt_of_ge h,shifted P]

def error (u : Fin (2^k)) (c : Nat → Fin (2^k)) (target : Fin (2^M P)) (n : Nat) (x : Fin (2^k)) :=
  if n<P.N then P.err u c n x else
    xor ((stateAt k u c P.r (inputWord u x).val).testBit (P.i+outIdx P n)) (target.val.testBit (outIdx P n))
lemma restrictGood {u : Fin (2^k)} {c : Nat → Fin (2^k)} {target : Fin (2^M P)} {x : Fin (2^k)} {n t : Nat}
    (gx : Good (error P u c target) n x) (h : t≤min n P.N) : Good (P.err u c) t x := by
  intro j hj
  simpa [error,show j<P.N by omega] using gx j (by omega)
lemma allTri (u : Fin (2^k)) (c : Nat → Fin (2^k)) (target : Fin (2^M P)) :
  ∀ n<L P, ∀ x y, Good (error P u c target) n x → Good (error P u c target) n y →
    (∀ b:Fin k, ¬Future (pv P) n (L P) b.val → x.val.testBit b.val=y.val.testBit b.val) →
    xor (error P u c target n x) (x.val.testBit (pv P n).val)=xor (error P u c target n y) (y.val.testBit (pv P n).val) := by
  intro n hn x y gx gy same
  by_cases inT:n<P.N
  · simp only [error,inT,ite_true,pvIn P inT]
    exact intervalTri P u c n inT x y (restrictGood P gx (by omega)) (restrictGood P gy (by omega)) (fun j hj ht => past P hn same j (by simpa [pos,inT] using hj) ht)
  · have done : P.a=P.r-5 := by by_contra h; simp [L,M,h] at hn; omega
    let j:=outIdx P n
    have jM : j<M P := by dsimp [j,outIdx,L] at *;omega
    have jLt : j<(summary P.v P.a).2-P.d := by simpa [M,done] using jM
    have tx := (P.goodIff u c x).mp (restrictGood P gx (by omega))
    have ty := (P.goodIff u c y).mp (restrictGood P gy (by omega))
    have te:=P.terminal u c (fun w pre => cutPrefix45 u c w (by have:=P.kLarge;omega) (P.big le_rfl) pre)
      done (inputWord u x) (inputWord u y) ⟨j,jLt⟩ tx ty (by
        intro b hb
        simp only [P.srcRecover]
        apply same b
        rintro ⟨t,hnt,ht,heq⟩
        rw [pvOut P (by omega)] at heq
        exact hb (outIdx P t) (by dsimp [j,outIdx];omega) heq)
    simp only [P.srcRecover] at te
    simp only [error,inT,ite_false,pvOut P (by omega : P.N≤n)]
    exact (show ∀ a b c d e:Bool, xor a b=xor c d → xor (xor a e) c=xor (xor b e) d by decide) _ _ _ _ _ te

lemma futureIff (b : Fin k) : Future (pv P) 0 (L P) b.val ↔ pivotBit P b.val=true := by
  rw [pivotSpec]
  constructor
  · rintro ⟨n,_,hn,h⟩
    by_cases hN:n<P.N
    · exact Or.inl ⟨⟨n,hN⟩,Fin.ext (by rwa [pvIn P hN] at h)⟩
    · right; refine ⟨⟨outIdx P n,by change outIdx P n<M P; dsimp [outIdx,L] at *;omega⟩,Fin.ext ?_⟩
      rw [pvOut P (by omega)] at h;exact h
  · rintro (⟨n,hn⟩|⟨j,hj⟩)
    · refine ⟨n.val,by omega,by have:=n.isLt;dsimp [L];omega,?_⟩
      rw [pvIn P n.isLt,hn]
    · let n:=L P-1-j.val
      have hlo : P.N≤n := by have:=j.isLt;change j.val<M P at this;dsimp [n,L];omega
      have hhi : n<L P := by have:=j.isLt;change j.val<M P at this;dsimp [n,L];omega
      have hidx : outIdx P n=j.val := by have:=j.isLt;change j.val<M P at this;dsimp [outIdx,n,L];omega
      refine ⟨n,by omega,hhi,?_⟩
      rw [pvOut P hlo,hidx];exact congrArg Fin.val hj
lemma bitsIff (u i m : Nat) (t : Fin (2^m)) : (u >>> i) % 2^m=t.val ↔ ∀ j<m, u.testBit (i+j)=t.val.testBit j := by
  constructor
  · intro h j hj
    simpa [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,hj] using congrArg (fun z : Nat => z.testBit j) h
  · intro ag
    apply Nat.eq_of_testBit_eq; intro j
    by_cases hj:j<m
    · simpa [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,hj] using ag j hj
    · have ht : t.val.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le t.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [Nat.testBit_mod_two_pow,hj,ht]
lemma allGood (u : Fin (2^k)) (c : Nat → Fin (2^k)) (target : Fin (2^M P)) (x : Fin (2^k)) :
    Good (error P u c target) (L P) x ↔
      (trace u c P.q (inputWord u x).val P.a).2.2=P.v ∧
      (stateAt k u c P.r (inputWord u x).val >>> P.i)%2^M P=target.val := by
  rw [bitsIff,← P.goodIff]
  constructor
  · intro gx
    refine ⟨restrictGood P gx (by dsimp [L];omega), ?_⟩
    intro j hj
    let n:=L P-1-j
    have hlo : P.N≤n := by dsimp [n,L];omega
    have hi : n<L P := by dsimp [n,L];omega
    have he : outIdx P n=j := by dsimp [outIdx,n,L];omega
    exact (Params.xorFalse ..).mp (by simpa only [error,Nat.not_lt_of_ge hlo,ite_false,he] using gx n hi)
  · rintro ⟨gx,go⟩ n hn
    by_cases h:n<P.N
    · simp [error,h,gx n h]
    · simp [error,h,go (outIdx P n) (by dsimp [outIdx,L] at *;omega)]
def getKey (c : Nat → Fin (2^k)) (seed : Fin (2^k)) (target : Fin (2^M P)) (u : Fin (2^k)) : Fin (2^k) :=
  inputWord u (run (pv P) (error P u c target) seed (L P))
theorem getKeySpec (c : Nat → Fin (2^k)) (seed : Fin (2^k)) (target : Fin (2^M P)) (u w : Fin (2^k)) :
  w=getKey P c seed target u ↔ (trace u c P.q w.val P.a).2.2=P.v ∧
    (∀ b:Fin k, pivotBit P b.val=false → (src u w.val).testBit b.val=seed.val.testBit b.val) ∧
      (stateAt k u c P.r w.val >>> P.i)%2^M P=target.val := by
  let x : Fin (2^k):=⟨src u w.val,Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) u.isLt⟩
  have inv : inputWord u x = w := Fin.ext (P.keyRecover u w)
  have cert := certified (pv P) (error P u c target) seed
    (fun _ hn _ ht he => distinct P hn ht he) (allTri P u c target) x
  rw [allGood,inv] at cert
  have eq : w=getKey P c seed target u ↔ x=run (pv P) (error P u c target) seed (L P) := by
    constructor
    · intro h
      apply Fin.ext
      change src u w.val=_
      rw [h];exact P.srcRecover ..
    · intro h;rw [←inv,h];rfl
  rw [eq,cert]
  have fb (b:Fin k) : (¬Future (pv P) 0 (L P) b.val) ↔ pivotBit P b.val=false := by rw [futureIff];cases pivotBit P b.val <;> decide
  simp only [fb]
  constructor
  · rintro ⟨⟨t,o⟩,s⟩;exact ⟨t,s,o⟩
  · rintro ⟨t,s,o⟩;exact ⟨⟨t,o⟩,s⟩

variable (c : Nat → Fin (2^k)) (seed : Fin (2^k)) (target : Fin (2^M P)) (u : Fin (2^k))
abbrev cutSource := cut P.q (word39 u (getKey P c seed target u))
lemma cutTranscript (j : Nat) (hj:j<P.a) :
    let f := cutSource P c seed target u
    let mode := (summary P.v j).1
    let t := tick j
    let e := edge P.q P.v j
    lineOne u c f mode t e=P.v.testBit (3*j) ∧
      lineTwo u c f mode t e=P.v.testBit (3*j+1) ∧
      lGuard u c f (t-1) e=P.v.testBit (3*j+2) := by
  let w:=getKey P c seed target u
  have spec := (getKeySpec P c seed target u w).mp rfl
  have pre := (traceIff u c _ _ P.hv).mp spec.1
  have eqs:=cutQueries45 u c w (by have:=P.kLarge;omega) (P.big (Nat.le_of_lt hj)) (fun j' hj' => pre j' (by omega))
  dsimp only at eqs ⊢
  change lineOne u c (cut P.q (word39 u w)) _ _ _=_ ∧ lineTwo u c (cut P.q (word39 u w)) _ _ _=_ ∧ lGuard u c (cut P.q (word39 u w)) _ _=_
  rw [←eqs.1,←eqs.2.1,←eqs.2.2]
  have group:= (P.group u c w.val j).mpr (pre j hj)
  refine ⟨?_,?_,?_⟩
  · simpa [Params.obs,show 3*j/3=j by omega] using group (0:Fin 3)
  · simpa [Params.obs,show (3*j+1)/3=j by omega,show (3*j+1)%3=1 by omega] using group (1:Fin 3)
  · simpa [Params.obs,show (3*j+2)/3=j by omega,show (3*j+2)%3=2 by omega] using group (2:Fin 3)
lemma cutTerminal (j : Nat) (hj:j<M P) :
    lineStep k u c (cutSource P c seed target u) P.r (k+P.i+j)=target.val.testBit j := by
  let w:=getKey P c seed target u
  let p:=k+P.i+j
  have spec:=(getKeySpec P c seed target u w).mp rfl
  have pre:=(traceIff u c _ _ P.hv).mp spec.1
  have done : P.a=P.r-5 := by by_contra h;simp [M,h] at hj
  have js : j<(summary P.v P.a).2-P.d := by simpa [M,done] using hj
  have hr:=P.hr; have hk:=P.hkd;have hd:=P.hd;have hl:=P.him
  have hpos : 2*P.r≤p := by dsimp [p];omega
  have gl := scan_gain_le P.v P.a 0
  change (summary P.v P.a).2≤2*P.a at gl
  have hi:P.i+j<k := by omega
  have hm : p % k=P.i+j := by dsimp [p];rw [show k+P.i+j=(P.i+j)+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
  have ep : p+3≤edge P.q P.v P.a := by dsimp [p,edge,Params.q];omega
  have eb : edge P.q P.v P.a+4≤P.q := by
    have big:=P.big (j:=P.a) (by omega)
    dsimp [edge];omega
  have base:=cutPrefix45 u c w (by have:=P.kLarge;omega) (P.big le_rfl) pre
  have right : lineStep k u c (word39 u w) P.r p=lineStep k u c (cut P.q (word39 u w)) P.r p := by
    rw [show P.r=(4+P.a)+1 by omega,PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq,
      PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq]
    unfold PEqualNP.Outside.L_meta_25545_aux.Line.Right.cell lInj
    rw [base _ (by omega),base _ (by omega),base _ (by omega),base _ (by omega),base _ (by omega)]
    simp [cut,show p+3-2*(4+P.a+1)<P.q by omega]
  have fromRaw:=Line.lineStep_eq_stateAt (by have:=P.kLarge;omega : 2≤k) u c w P.r p hpos
  rw [hm] at fromRaw
  exact right.symm.trans (fromRaw.trans ((bitsIff _ _ _ target).mp spec.2.2 j hj))
lemma nonpivotSource (b : Fin k) (hb:pivotBit P b.val=false) :
    (src u (getKey P c seed target u).val).testBit b.val=seed.val.testBit b.val :=
  ((getKeySpec P c seed target u _).mp rfl).2.1 b hb

end PEqualNP.Outside.L_meta_25571_aux.Semantics

namespace PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {R : Type} {k : Nat}

structure Context (k : Nat) (R : Type) where
  inputs : R → List Bool
  len : ∀ x, (inputs x).length = k

def Available (X : Context k R) (C : Circuit) (f : R → Bool) : Prop :=
  ∃ i < k + C.size, ∀ x, (C.wires (X.inputs x)).getD i false = f x

structure Valid (k : Nat) (C : Circuit) : Prop where
  fan : FanInTwo C
  back : ReadsBack k C

lemma wiresLen (C : Circuit) (xs : List Bool) : (C.wires xs).length = xs.length + C.size := by
  rcases C with ⟨gs,o⟩
  unfold Circuit.wires Circuit.size
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, List.length_cons]; rw [ih]; simp; omega

def Extends (X : Context k R) (C D : Circuit) (s : Nat) :=
  Valid k D ∧ D.size = C.size + s ∧ ∀ f, Available X C f → Available X D f

def gate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], 0⟩

lemma addGate (X : Context k R) {C : Circuit} (h : Valid k C) (g : Gate)
    (basis : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) (two : g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < k + C.size) :
    Extends X C (gate C g) 1 ∧ Available X (gate C g) (fun x => g.op.eval (g.inputs.map fun i => (C.wires (X.inputs x)).getD i false)) := by
  have he (x : R) : ((gate C g).wires (X.inputs x)) = (C.wires (X.inputs x)) ++ [g.op.eval (g.inputs.map fun i => (C.wires (X.inputs x)).getD i false)] := by
    simp [gate,Circuit.wires]
  have hs : (gate C g).size = C.size + 1 := by simp [gate,Circuit.size]
  have hl (x : R) : (C.wires (X.inputs x)).length = k+C.size := by rw [wiresLen,X.len]
  refine ⟨⟨⟨?_,?_⟩,hs,?_⟩,?_⟩
  · intro v hv
    simp [gate] at hv
    rcases hv with hv|rfl
    · exact h.fan v hv
    · exact ⟨basis,two⟩
  · intro j hj i hi
    simp [gate] at hj
    unfold gateAt at hi
    by_cases hj' : j < C.gates.length
    · simp [gate, List.getD_eq_getElem?_getD, List.getElem?_append_left hj'] at hi
      apply h.back j hj' i
      simpa [gateAt, List.getD_eq_getElem?_getD] using hi
    · have eq : j=C.gates.length := by omega
      subst j
      simp [gate,List.getD_eq_getElem?_getD] at hi
      exact back i hi
  · rintro f ⟨i,hi,heq⟩
    refine ⟨i, by omega, fun x => ?_⟩
    have hi' : i < (C.wires (X.inputs x)).length := by rwa [hl]
    simpa [he,List.getD_eq_getElem?_getD,List.getElem?_append_left hi'] using heq x
  · refine ⟨k+C.size, by omega, fun x => ?_⟩
    rw [he, ← hl x]; simp [List.getD_eq_getElem?_getD]

abbrev Build (X : Context k R) (C : Circuit) (s : Nat) (f : R → Bool) :=
  ∃ D, Extends X C D s ∧ Available X D f

lemma Extends.trans {X : Context k R} {A B C : Circuit} {s t : Nat}
    (a : Extends X A B s) (b : Extends X B C t) : Extends X A C (s+t) :=
  ⟨b.1, by rw [b.2.1,a.2.1,Nat.add_assoc], fun f h => b.2.2 _ (a.2.2 f h)⟩

namespace Build
variable {X : Context k R} {C : Circuit} {f g : R → Bool}

lemma leaf (h : Valid k C) (hf : Available X C f) : Build X C 0 f :=
  ⟨C,⟨h,rfl,fun _ => id⟩,hf⟩

lemma const (h : Valid k C) (v : Bool) : Build X C 1 (fun _ => v) := by
  cases v
  · exact ⟨_, addGate X h ⟨.or,[]⟩ (by simp) (by decide) (by simp)⟩
  · exact ⟨_, addGate X h ⟨.and,[]⟩ (by simp) (by decide) (by simp)⟩

lemma neg (h : Valid k C) (hf : Available X C f) : Build X C 1 (fun x => !f x) := by
  obtain ⟨i,hi,e⟩ := hf
  simp only [List.getD_eq_getElem?_getD] at e
  obtain ⟨a,b⟩ := addGate X h ⟨.not,[i]⟩ (by simp) (by simp) (by simpa using hi)
  exact ⟨_,a,by simpa [GateOp.eval,e] using b⟩

lemma conj (h : Valid k C) (hf : Available X C f) (hg : Available X C g) : Build X C 1 (fun x => (f x && g x)) := by
  obtain ⟨i,hi,ei⟩ := hf
  obtain ⟨j,hj,ej⟩ := hg
  simp only [List.getD_eq_getElem?_getD] at ei ej
  obtain ⟨a,b⟩ := addGate X h ⟨.and,[i,j]⟩ (by simp) (by simp) (by simp [hi,hj])
  exact ⟨_,a,by simpa [GateOp.eval,ei,ej] using b⟩

lemma disj (h : Valid k C) (hf : Available X C f) (hg : Available X C g) : Build X C 1 (fun x => (f x || g x)) := by
  obtain ⟨i,hi,ei⟩ := hf
  obtain ⟨j,hj,ej⟩ := hg
  simp only [List.getD_eq_getElem?_getD] at ei ej
  obtain ⟨a,b⟩ := addGate X h ⟨.or,[i,j]⟩ (by simp) (by simp) (by simp [hi,hj])
  exact ⟨_,a,by simpa [GateOp.eval,ei,ej] using b⟩

lemma xorGate (h : Valid k C) (hf : Available X C f) (hg : Available X C g) : Build X C 4 (fun x => xor (f x) (g x)) := by
  obtain ⟨A,a,ha⟩ := conj h hf hg
  obtain ⟨B,b,hb⟩ := neg a.1 ha
  obtain ⟨D,d,hd⟩ := disj b.1 ((a.trans b).2.2 _ hf) ((a.trans b).2.2 _ hg)
  obtain ⟨E,e,he⟩ := conj d.1 hd (d.2.2 _ hb)
  have eq (v w : Bool) : ((v || w) && !(v && w)) = xor v w := by cases v <;> cases w <;> rfl
  exact ⟨_,((a.trans b).trans d).trans e,by simpa only [eq] using he⟩

end Build

inductive Op where | band | bor | bxor

def Op.cost : Op → Nat | .bxor => 4 | _ => 1
def Op.eval : Op → Bool → Bool → Bool | .band => and | .bor => or | .bxor => xor

inductive Expr (α : Type) where
  | var (v : α)
  | lit (b : Bool)
  | inv (e : Expr α)
  | bin (op : Op) (a b : Expr α)

namespace Expr
variable {α : Type}
def cost : Expr α → Nat
  | .var _ => 0 | .lit _ => 1 | .inv e => e.cost + 1
  | .bin op a b => (a.cost + b.cost) + op.cost

def eval (env : α → Bool) : Expr α → Bool
  | .var v => env v | .lit b => b | .inv e => !(e.eval env)
  | .bin op a b => op.eval (a.eval env) (b.eval env)

theorem compile (X : Context k R) (env : α → R → Bool) (e : Expr α) {C : Circuit}
    (h : Valid k C) (read : ∀ v, Available X C (env v)) :
    Build X C e.cost (fun x => e.eval (fun v => env v x)) := by
  induction e generalizing C with
  | var v => exact Build.leaf h (read v)
  | lit b => exact Build.const h b
  | inv a ih =>
    obtain ⟨A,aa,ha⟩ := ih h read
    obtain ⟨B,bb,hb⟩ := Build.neg aa.1 ha
    exact ⟨_,aa.trans bb,hb⟩
  | bin op a b ia ib =>
    obtain ⟨A,aa,ha⟩ := ia h read
    obtain ⟨B,bb,hb⟩ := ib aa.1 (fun v => aa.2.2 _ (read v))
    have h' := bb.2.2 _ ha
    have build : Build X B op.cost (fun x => op.eval (a.eval (fun v => env v x)) (b.eval (fun v => env v x))) := by
      cases op
      · exact Build.conj bb.1 h' hb
      · exact Build.disj bb.1 h' hb
      · exact Build.xorGate bb.1 h' hb
    obtain ⟨D,dd,hd⟩ := build
    exact ⟨_,(aa.trans bb).trans dd,hd⟩
end Expr

abbrev Ref (k j : Nat) := Fin k ⊕ Fin j

def env (X : Context k R) (node : Nat → R → Bool) {j : Nat} : Ref k j → R → Bool
  | .inl p => fun x => (X.inputs x).getD p.val false
  | .inr p => node p.val

theorem compileNetwork (X : Context k R) (node : Nat → R → Bool)
    (N : Nat) (program : (j : Nat) → Expr (Ref k j))
    (ok : ∀ j < N, ∀ x, node j x = (program j).eval (fun v => env X node v x)) :
    ∃ C, Valid k C ∧ C.size = ∑ j ∈ Finset.range N, (program j).cost ∧
      ∀ j<N, Available X C (node j) := by
  let inp := fun p : Fin k => fun x => (X.inputs x).getD p.val false
  have buildPrefix : ∀ t ≤ N, ∃ C, Valid k C ∧ C.size = ∑ j ∈ Finset.range t, (program j).cost ∧
      (∀ j<t, Available X C (node j)) ∧ (∀ p, Available X C (inp p)) := by
    intro t; induction t with
    | zero =>
      intro _; let C : Circuit := ⟨[],0⟩
      refine ⟨C,⟨by simp [FanInTwo,C],by simp [ReadsBack,C]⟩,?_,by simp,?_⟩
      · simp [C,Circuit.size]
      · exact fun p => ⟨p.val,p.isLt,fun x => rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨C,vc,hc,old,ins⟩ := ih (by omega)
      have reads : ∀ v : Ref k t, Available X C (env X node v) := by
        intro v; cases v with
        | inl p => exact ins p
        | inr p => exact old p p.isLt
      obtain ⟨D,ext,hd⟩ := (program t).compile X (env X node) vc reads
      refine ⟨D,ext.1,by rw [ext.2.1,hc,Finset.sum_range_succ],?_,fun p => ext.2.2 _ (ins p)⟩
      intro j hj
      by_cases eq : j=t
      · subst j; have e := funext (ok t (by omega)); rwa [e]
      · exact ext.2.2 _ (old j (by omega))
  obtain ⟨C,v,s,a,_⟩ := buildPrefix N (by rfl)
  exact ⟨C,v,s,a⟩

theorem select {X : Context k R} {C : Circuit} {β : Type} {f : β → R → Bool}
    (h : ∀ b, Available X C (f b)) :
    ∃ wire : β → Fin (k+C.size), ∀ x b, (C.wires (X.inputs x)).getD (wire b).val false = f b x := by
  choose a ha he using h
  exact ⟨fun b => ⟨a b,ha b⟩,fun x b => he b x⟩

namespace Local
open Expr
variable {α : Type}

def flip (x : Expr α) (b : Bool) : Expr α := if b then .inv x else x
@[simp] theorem eval_flip (v : α → Bool) (x : Expr α) (b : Bool) :
    (flip x b).eval v = xor (x.eval v) b := by cases b <;> simp [flip,Expr.eval]
theorem cost_flip (x : Expr α) (b : Bool) : (flip x b).cost ≤ x.cost + 1 := by cases b <;> simp [flip,Expr.cost]

def tr (a b c : Expr α) : Expr α := .bin .bxor (.bin .bxor a b) c

def core (a b c d e : α) : Expr α := .bin .bxor (tr (.var a) (.var b) (.var c))
  (.bin .band (.inv (tr (.var b) (.var c) (.var d))) (tr (.var c) (.var d) (.var e)))

def inj (src row : α) (cn : Bool) : Expr α := flip (.bin .bxor (.var src) (.var row)) cn

def cell (a b c d e src row : α) (cn : Bool) : Expr α := .bin .bxor (core a b c d e) (inj src row cn)

theorem coreCost (a b c d e : α) : (core a b c d e).cost = 30 := rfl

theorem cellCost (a b c d e s u : α) (cn : Bool) :
    (cell a b c d e s u cn).cost = 38 + cn.toNat := by cases cn <;> rfl

theorem cellEval (v : α → Bool) (a b c d e s u : α) (cn : Bool) :
    (cell a b c d e s u cn).eval v =
      xor (xor (xor (xor (v a) (v b)) (v c))
         (!(xor (xor (v b) (v c)) (v d)) && xor (xor (v c) (v d)) (v e)))
        (xor (xor (v s) (v u)) cn) := by simp [cell,core,inj,tr,Expr.eval,Op.eval]

theorem budget {k r d : Nat} (hr : 6≤r) (hkd : k+3+d=5*r) (hd : d≤r-5) :
    64 * (k+3*r+1) * (r+1) + 96 * (k+1) ≤ 128 * (k+1) * (r+1) := by
  have hwidth : 64*(k+3*r+1) ≤ 112*(k+1) := by omega
  have hfixed : 96 ≤ 16*(r+1) := by omega
  calc
    _ ≤ (112*(k+1))*(r+1) + (16*(r+1))*(k+1) := Nat.add_le_add
      (Nat.mul_le_mul_right _ hwidth) (Nat.mul_le_mul_right _ hfixed)
    _ = _ := by ring

end Local

lemma inputAvailable (X : Context k R) (C : Circuit) (p : Fin k) :
    Available X C (fun x => (X.inputs x).getD p.val false) := by
  refine ⟨p.val,by have := p.isLt; omega, fun x => ?_⟩
  have aux (w : List Bool) (hw : p.val < w.length) (gs : List Gate) :
      ((⟨gs,0⟩ : Circuit).wires w).getD p.val false = w.getD p.val false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((⟨gs,0⟩ : Circuit).wires (w ++ [_])).getD p.val false = _
      rw [ih _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hw]
  exact aux (X.inputs x) (by rw [X.len]; exact p.isLt) C.gates

lemma buildAll {X : Context k R} {C : Circuit} (vc : Valid k C) (b n : Nat) (f : Fin n → R → Bool)
    (each : ∀ D : Circuit, Valid k D → (∀ g, Available X C g → Available X D g) →
      ∀ i : Fin n, Build X D b (f i)) :
    ∃ D, Extends X C D (b*n) ∧ ∀ i, Available X D (f i) := by
  have grow (t : Nat) (ht : t≤n) : ∃ D, Extends X C D (b*t) ∧
      ∀ i : Fin n, i.val<t → Available X D (f i) := by
    induction t with
    | zero => exact ⟨C,⟨vc,by simp,fun _ => id⟩,by simp⟩
    | succ t ih =>
      obtain ⟨D,dd,hp⟩ := ih (by omega)
      let j : Fin n := ⟨t,by omega⟩
      obtain ⟨E,ee,hu⟩ := each D dd.1 dd.2.2 j
      refine ⟨E,by simpa only [Nat.mul_succ] using dd.trans ee,?_⟩
      intro i hi
      by_cases h : i.val=t
      · simpa only [show i=j from Fin.ext h] using hu
      · exact ee.2.2 _ (hp i (by omega))
  obtain ⟨D,dd,h⟩ := grow n (by rfl)
  exact ⟨D,dd,fun i => h i i.isLt⟩

namespace Local

lemma budget72 {k r d : Nat} (hr : 6≤r) (hkd : k+3+d=5*r) (hd : d≤r-5) :
    72*(k+3*r+1)*(r+1) + 4*k ≤ 128*(k+1)*(r+1) := by
  have hwidth : 72*(k+3*r+1) ≤ 126*(k+1) := by omega
  have hfixed : 4 ≤ 2*(r+1) := by omega
  calc
    _ ≤ (126*(k+1))*(r+1) + (2*(r+1))*(k+1) := Nat.add_le_add
      (Nat.mul_le_mul_right _ hwidth) (Nat.mul_le_mul hfixed (by omega))
    _ = _ := by ring
end Local

end PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram

namespace PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_25545_aux.Line
open PEqualNP.Outside.L_meta_25545_aux.Word.Layout

def rowCtx (k : Nat) : Context k (Fin (2^k)) where
  inputs u := (List.range k).map (fun i => u.val.testBit i)
  len := by simp

lemma rowsAvailable {k : Nat} (C : Circuit) (i : Fin k) :
    Available (rowCtx k) C (fun u => u.val.testBit i.val) := by
  have h := inputAvailable (rowCtx k) C i
  simpa [rowCtx,List.getD_eq_getElem?_getD,i.isLt] using h

lemma exposeRaw {k : Nat} {C : Circuit} (hc : Valid k C)
    (x : Fin (2^k) → Fin (2^k)) (ready : ∀ i : Fin k, Available (rowCtx k) C (fun u => (x u).val.testBit i.val)) :
    ∃ D : Circuit, Valid k D ∧ D.size = C.size+4*k ∧
      ∃ w : Fin k → Fin (k+D.size), ∀ u i,
        (D.wires ((rowCtx k).inputs u)).getD (w i).val false = (inputWord u (x u)).val.testBit i.val := by
  let f := fun i : Fin k => fun u : Fin (2^k) => (inputWord u (x u)).val.testBit i.val
  have each (D : Circuit) (vd : Valid k D) (ext : ∀ g, Available (rowCtx k) C g → Available (rowCtx k) D g)
      (i : Fin k) : Build (rowCtx k) D 4 (f i) := by
    let p : Fin k := ⟨(i.val +k -(k-1)%k)%k, Nat.mod_lt _ (by have := i.isLt; omega)⟩
    have eq (u : Fin (2^k)) : f i u = xor ((x u).val.testBit p.val) (u.val.testBit p.val) := by
      change (rot k (k-1) ((x u).val ^^^ u.val)).testBit i.val = _
      rw [testBit_rot (Nat.xor_lt_two_pow (x u).isLt u.isLt) i.isLt, Nat.testBit_xor]
    rw [funext eq]
    exact Build.xorGate vd (ext _ (ready p)) (rowsAvailable D p)
  obtain ⟨D,ext,outs⟩ := buildAll hc 4 k f each
  exact ⟨D,ext.1,ext.2.1,select outs⟩

end PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram

namespace PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep cut lInj lGuard)

def h (v : Nat) := max v (2*v-3)
def e (v z : Nat) := z-h v
def slot (B r v z : Nat) := (B-e v z)*(r+1)+v
def active (A B r v z : Nat) : Prop := v≤r ∧ A+h v≤z ∧ z+3*v≤B
def jobs (A B r : Nat) := (B-A+1)*(r+1)

lemma within {A B r v z : Nat} (hz : active A B r v z) : slot B r v z < jobs A B r := by
  obtain ⟨vr,az,zb⟩:=hz
  have ee : A ≤ e v z := by unfold e;omega
  have le : (B-e v z)*(r+1) ≤ (B-A)*(r+1) := Nat.mul_le_mul_right _ (by omega)
  unfold slot jobs; rw [Nat.add_mul];omega

lemma before {B r v z w y : Nat} (hy : e w y≤B) (hw:w≤r)
    (earlier : e v z<e w y ∨ (e v z=e w y ∧ w<v)) : slot B r w y < slot B r v z := by
  unfold slot
  rcases earlier with h|⟨hr,hv⟩
  · have le : (B-e w y+1)*(r+1) ≤ (B-e v z)*(r+1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul,Nat.one_mul] at le;omega
  · rw [hr];omega

lemma predRank {s z y : Nat} (lo:h (s+1)≤z) (h1:z-1≤y) : e (s+1) z≤e s y := by unfold e h at *;omega
lemma predStrict {s z y : Nat} (hs:3≤s) (lo:h (s+1)≤z) (h1:z-1≤y) : e (s+1) z<e s y := by unfold e h at *;omega
lemma predActive {A B r s z y : Nat} (hz:active A B r (s+1) z) (h1:z-1≤y) (h2:y≤z+3) : active A B r s y := by unfold active h at *;omega
lemma predEarlier {A B r s z y : Nat} (hz:active A B r (s+1) z) (h1:z-1≤y) (h2:y≤z+3) : slot B r s y < slot B r (s+1) z := by
  obtain ⟨vr,az,zb⟩ := hz
  apply before (by unfold e;omega) (by omega)
  have:= predRank (by omega : h (s+1)≤z) h1
  omega
lemma predBeforeProbe {A B r s z y : Nat} (hz:active A B r (s+1) z) (hs:3≤s) (h1:z-1≤y) (h2:y≤z+3) : slot B r s y < slot B r 0 (e (s+1) z) := by
  obtain ⟨vr,az,zb⟩ := hz
  apply before (by unfold e;omega) (by omega)
  exact Or.inl (by simpa [e,h] using predStrict hs (by omega : h (s+1)≤z) h1)
def injPos (s z : Nat) := z+1-2*s
lemma injActive {A B r s z : Nat} (hz:active A B r (s+1) z) : active A B r 0 (injPos s z) := by unfold active injPos h at *;omega
lemma injEarlier {A B r s z : Nat} (hz:active A B r (s+1) z) : slot B r 0 (injPos s z) < slot B r (s+1) z := by
  obtain ⟨vr,az,zb⟩ := hz
  apply before (by unfold e injPos; omega) (by omega)
  unfold e injPos h at *;omega
lemma injDiag {s z : Nat} (hs:2≤s) : injPos s z=e (s+1) z := by unfold injPos e h;omega

lemma jobs_eq (k q r : Nat) (hq:k≤q) : jobs (q-k) (q+3*r) r = (k+3*r+1)*(r+1) := by
  unfold jobs;congr 1;omega

def unrankE (B r j : Nat) := B-j/(r+1)
def unrankV (r j : Nat) := j%(r+1)
lemma decode {B r v z:Nat} (vr:v≤r) (hz:h v≤z) (zb:z≤B) :
    unrankV r (slot B r v z)=v ∧ unrankE B r (slot B r v z)+h v=z := by
  unfold unrankV unrankE slot
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega), Nat.mul_comm (B-e v z) (r+1), Nat.mul_add_div (by omega : 0<r+1), Nat.div_eq_of_lt (by omega : v<r+1)]
  unfold e;omega

open PEqualNP.Outside.L_meta_25545_aux.Scan (summary)
variable {k : Nat} (P : Params k)
abbrev A := P.q-k
abbrev B := P.q+3*P.r
abbrev Active := active (A P) (B P) P.r
abbrev Slot := slot (B P) P.r
abbrev Jobs := jobs (A P) (B P) P.r
abbrev time (j : Nat) := tick j-1
abbrev stop (j : Nat) := edge P.q P.v j
abbrev col (j b : Nat) := stop P j-b

theorem probeRank (j b : Nat) (hj:j<P.a) (hb:b<3) : e (time j) (col P j b)=P.pp (3*j+b) := by
  have := (Bridge.bounds P.q P.v j (P.big (by omega))).1
  simp only [Params.pp,show (3*j+b)/3=j by omega,show (3*j+b)%3=b by omega]
  unfold col stop time e h left tick at *;omega

theorem probeActive (j b : Nat) (hj:j<P.a) (hb:b<3) : Active P (time j) (col P j b) := by
  have inter := (P.interval (n:=3*j+b) (by dsimp [Params.N];omega)).1
  have rankeq := probeRank P j b hj hb
  have bounds := Bridge.bounds P.q P.v j (P.big (by omega))
  have ar:=P.ha; have hr:=P.hr
  unfold Active active A B e col stop time h tick at *;omega

theorem sideActive {s z d : Nat} (hc:Active P s z) (hz:z+3*s+d≤B P) : Active P s (z+d) := by unfold Active active at *;omega
lemma sideBefore {s z d : Nat} (hc:Active P s z) (hz:z+3*s+d≤B P) (hd:0<d) : Slot P s (z+d) < Slot P 0 (e s z) := by
  obtain ⟨_,_,_⟩ := hc
  apply before (by unfold e;omega) (by omega)
  exact Or.inl (by change z-h s<z+d-h s;omega)

lemma oldMixActive {j y : Nat} (hj:j<P.a) (lo:stop P j≤y) (hi:y≤stop P j+2) : Active P (tick j-2) y := by
  have a := probeActive P j 0 hj (by decide)
  apply predActive (s:=tick j-2) (z:=col P j 0) ?_ (by unfold col;omega) (by unfold col;omega)
  simpa only [show tick j-2+1=time j by unfold time tick;omega] using a
lemma oldMixBefore {j y : Nat} (hj:j<P.a) (lo:stop P j≤y) (hi:y≤stop P j+2) : Slot P (tick j-2) y < Slot P 0 (P.pp (3*j+0)) := by
  rw [←probeRank P j 0 hj (by decide), show time j=tick j-2+1 by unfold time tick;omega]
  apply predBeforeProbe (A:=A P) ?_ (by unfold tick;omega) (by unfold col;omega) (by unfold col;omega)
  simpa only [show tick j-2+1=time j by unfold time tick;omega] using probeActive P j 0 hj (by decide)

lemma extInj {j b d : Nat} (hj:j<P.a) (hb:b<3) (d1:1≤d) (d2:d≤2) :
    let y := stop P j+d+3-2*time j
    Active P 0 y ∧ Slot P 0 y < Slot P 0 (P.pp (3*j+b)) := by
  intro y
  have rankeq := probeRank P j b hj hb
  have a := probeActive P j b hj hb
  have bds := Bridge.bounds P.q P.v j (P.big (by omega))
  unfold Active active col A B time e h stop tick at *
  dsimp only [y,time,stop,tick] at *
  constructor
  · omega
  · apply before (by unfold B e h;omega) (by omega);left;unfold e h;omega

lemma hitExtra {j b : Nat} (hj:j<P.a) (hb:b<2) :
    Active P (time j) (col P j b) ∧ Slot P (time j) (col P j b) < Slot P 0 (P.pp (3*j+2)) := by
  have a:=probeActive P j b hj (by omega)
  refine ⟨a,?_⟩
  obtain ⟨vr,lo,hi⟩:=a
  apply before (by unfold e;omega) vr;left
  have h1:=probeRank P j b hj (by omega)
  simp only [e,h,Nat.mul_zero,Nat.zero_sub,Nat.max_self,Nat.sub_zero]
  have d:=P.decreasing (j:=3*j+b) (t:=3*j+2) (by omega) (by unfold Params.N;omega)
  simpa only [e,h] using (lt_of_lt_of_eq d h1.symm)

abbrev M := if P.a=P.r-5 then (summary P.v P.a).2-P.d else 0
abbrev outZ (j : Nat) := k+P.i+j
lemma targetActive {j : Nat} (hj:j<M P) : Active P P.r (outZ P j) ∧ e P.r (outZ P j)=A P+j := by
  have bound := PEqualNP.Outside.L_meta_25545_aux.Scan.scan_gain_le P.v P.a 0
  change (summary P.v P.a).2≤2*P.a at bound
  have ar:=P.ha; have hr:=P.hr;have kd:=P.hkd;have idd:=P.him;have hd:=P.hd
  have done : P.a=P.r-5 := by by_contra h;simp [M,h] at hj
  rw [done] at bound; simp only [M,done,ite_true] at hj
  unfold Active active B A outZ h e Params.q;unfold h;omega

end PEqualNP.Outside.L_meta_25571_aux.Rank

namespace PEqualNP.Outside.L_meta_25571_aux.Grid
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep)
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
open PEqualNP.CircuitLowerBounds
variable {k:Nat} (P : Params k)
abbrev Row (k : Nat) := Fin (2^k)
variable (c : Nat → Row k) (f : Row k → Nat → Bool)
def val (v z : Nat) (u : Row k) := lineStep k u c (f u) v z
noncomputable def node (j : Nat) (u : Row k) : Bool := by
  classical
  let v := unrankV P.r j
  let z := unrankE (B P) P.r j + h v
  exact if Active P v z then val c f v z u else false
lemma nodeAt {v z : Nat} (hc:Active P v z) (u : Row k) : node P c f (Slot P v z) u = val c f v z u := by
  have d:=decode (B:=B P) hc.1 (by have:=hc.2.1;omega : h v≤z) (by have:=hc.2.2;omega : z≤B P)
  simp only [node,d.1,d.2,hc,ite_true]

def Can (j : Nat) (g : Row k → Bool) := ∃ E : Expr (Ref k j), E.cost ≤ 72 ∧ ∀ u, E.eval (fun a => env (rowCtx k) (node P c f) a u) = g u

def rowRef (y : Nat) : Ref k j := .inl ⟨y%k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
lemma rowEval (y : Nat) (u : Row k) : env (rowCtx k) (node P c f) (rowRef P (j:=j) y) u=u.val.testBit (y%k) := by
  simp [env,rowRef,rowCtx,List.getD_eq_getElem?_getD,Nat.mod_lt _ (by have:=P.kLarge;omega : 0<k)]

def prevRef (v z : Nat) (lt:Slot P v z<j) : Ref k j := .inr ⟨Slot P v z,lt⟩
lemma prevEval (hc:Active P v z) (lt:Slot P v z<j) (u : Row k) : env (rowCtx k) (node P c f) (prevRef P v z lt) u=val c f v z u := nodeAt P c f hc u

lemma canSucc {s z : Nat} (hc:Active P (s+1) z) : Can P c f (Slot P (s+1) z) (val c f (s+1) z) := by
  let ref (y : Nat) (h₁:z-1≤y) (h₂:y≤z+3) := prevRef P s y (predEarlier hc h₁ h₂)
  let x := prevRef P 0 (injPos s z) (injEarlier hc)
  let u0 := rowRef P (j:=Slot P (s+1) z) (injPos s z)
  let cn := (c (s+1)).val.testBit (z%k)
  refine ⟨Local.cell (ref (z-1) (by omega) (by omega)) (ref z (by omega) (by omega)) (ref (z+1) (by omega) (by omega)) (ref (z+2) (by omega) (by omega)) (ref (z+3) (by omega) (by omega)) x u0 cn, ?_,?_⟩
  · rw [Local.cellCost];cases cn <;> decide
  · intro u
    have eqr (y) (h₁:z-1≤y) (h₂:y≤z+3) : env (rowCtx k) (node P c f) (ref y h₁ h₂) u=val c f s y u := prevEval P c f (predActive hc h₁ h₂) _ u
    have eqx : env (rowCtx k) (node P c f) x u = f u (injPos s z) := prevEval P c f (injActive hc) _ u
    rw [Local.cellEval];simp only [eqr,eqx,u0,rowEval,val,cn,injPos,Line.lineStep_succ]
    simp only [Bool.xor_comm, Bool.xor_assoc, Bool.xor_left_comm]

lemma slotDecoded (j : Nat) (hj:j<Jobs P) : Slot P (unrankV P.r j) (unrankE (B P) P.r j + h (unrankV P.r j)) = j := by
  have hb : j/(P.r+1)<B P-A P+1 := Nat.div_lt_of_lt_mul (show j<(P.r+1)*(B P-A P+1) by rw [Nat.mul_comm]; exact hj)
  have cap : j/(P.r+1) ≤ B P := by omega
  have hm := Nat.mod_add_div j (P.r+1)
  simp only [Slot,slot,unrankE,unrankV,e,Nat.add_sub_cancel]
  rw [Nat.sub_sub_self (show j/(P.r+1)≤B P from cap),Nat.mul_comm];omega

theorem build (base : ∀ z, Active P 0 z → Can P c f (Slot P 0 z) (fun u => f u z)) :
    ∃ C : Circuit, Valid k C ∧ C.size≤72*(k+3*P.r+1)*(P.r+1) ∧
      ∀ v z, Active P v z → Available (rowCtx k) C (val c f v z) := by
  classical
  have cand (j : Nat) : ∃ E : Expr (Ref k j), E.cost ≤ 72 ∧ ∀ u, j<Jobs P → E.eval (fun a=>env (rowCtx k) (node P c f) a u) = node P c f j u := by
    by_cases hj : j<Jobs P
    · let v := unrankV P.r j
      let z := unrankE (B P) P.r j+h v
      have eqj : Slot P v z = j := slotDecoded P j hj
      by_cases a : Active P v z
      · have can : Can P c f (Slot P v z) (val c f v z) := by
          cases hv : v with
          | zero => rw [hv] at a; exact base z a
          | succ s => rw [hv] at a; exact canSucc P c f a
        rw [eqj] at can
        obtain ⟨E,le,ev⟩ := can
        exact ⟨E,le,fun u _ => (ev u).trans (by rw [←eqj,nodeAt P c f a])⟩
      · refine ⟨.lit false,by change 1≤72;decide,?_⟩;intro u _
        change false=(if Active P v z then val c f v z u else false);simp [a]
    · exact ⟨.lit false,by change 1≤72;decide,fun _ h=>False.elim (hj h)⟩
  choose E cost ev using cand
  obtain ⟨C,valid,size,av⟩:=compileNetwork (rowCtx k) (node P c f) (Jobs P) E (fun j hj u=>(ev j u hj).symm)
  refine ⟨C,valid,?_,?_⟩
  · rw [size]; calc
      _ ≤ ∑ _j ∈ Finset.range (Jobs P), (72:Nat) := Finset.sum_le_sum (fun j _ => cost j)
      _ = _ := by
        have hq:k≤P.q := by have:=P.hd;unfold Params.q;omega
        simp only [Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul,Jobs,A,B,jobs_eq k _ _ hq];ring
  · intro v z a
    have := av _ (within a)
    rwa [show node P c f (Slot P v z)=val c f v z from funext (nodeAt P c f a)] at this

end PEqualNP.Outside.L_meta_25571_aux.Grid

namespace PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram.Local
open Expr
variable {α : Type}

def base (a b c d e row : α) (cn : Bool) : Expr α := flip (.bin .bxor (core a b c d e) (.var row)) cn

def solveOut (a b c d e row : α) (cn want : Bool) := flip (base a b c d e row cn) want

def solveHit (a b c d e row y1 y2 : α) (cn want : Bool) :=
  flip (tr (base a b c d e row cn) (.var y1) (.var y2)) want

def solveTwo (a b c d e row s3 u3 : α) (cn c3 want : Bool) :=
  flip (.bin .bxor (base a b c d e row cn) (inj s3 u3 c3)) (!want)

def solveOne (a b c d e row s1 u1 s2 u2 : α) (cn c1 c2 want : Bool) :=
  flip (.bin .bxor (tr (base a b c d e row cn) (tr (.var b) (.var c) (.var d)) (inj s1 u1 c1))
    (inj s2 u2 c2)) want

theorem solveOut_cost (a b c d e u : α) (cn w : Bool) : (solveOut a b c d e u cn w).cost ≤ 36 := by
  cases cn <;> cases w <;> exact of_decide_eq_true rfl

theorem solveHit_cost (a b c d e u y1 y2 : α) (cn w : Bool) : (solveHit a b c d e u y1 y2 cn w).cost ≤ 44 := by
  cases cn <;> cases w <;> exact of_decide_eq_true rfl

theorem solveTwo_cost (a b c d e u s3 u3 : α) (cn c3 w : Bool) : (solveTwo a b c d e u s3 u3 cn c3 w).cost ≤ 45 := by
  cases cn <;> cases c3 <;> cases w <;> exact of_decide_eq_true rfl

theorem solveOne_cost (a b c d e u s1 u1 s2 u2 : α) (cn c1 c2 w : Bool) :
    (solveOne a b c d e u s1 u1 s2 u2 cn c1 c2 w).cost ≤ 66 := by
  cases cn <;> cases c1 <;> cases c2 <;> cases w <;> exact of_decide_eq_true rfl

private theorem xorRegroup (c p u t : Bool) : xor c (xor (xor p u) t) = xor p (xor (xor c u) t) := by
  cases c <;> cases p <;> cases u <;> cases t <;> rfl

theorem withPivot (v : α → Bool) (a b c d e s row : α) (cn : Bool) :
    (cell a b c d e s row cn).eval v = xor (v s) ((base a b c d e row cn).eval v) := by
  simp only [cell,base,inj,Expr.eval,Op.eval,eval_flip]; exact xorRegroup ..

private theorem outAlg (p b w : Bool) (h : xor p b=w) : xor b w=p := by cases p <;> cases b <;> cases w <;> simp_all
private theorem hitAlg (p b v1 v2 w : Bool) (h : xor (xor (xor p b) v1) v2=w) :
    xor (xor (xor b v1) v2) w=p := by cases p <;> cases b <;> cases v1 <;> cases v2 <;> cases w <;> simp_all
private theorem twoAlg (p b j w : Bool) (h : ((xor p b) == j)=w) :
    xor (xor b j) (!w)=p := by cases p <;> cases b <;> cases j <;> cases w <;> simp_all
private theorem oneAlg (p b g j1 j2 w : Bool) (h : ((xor p b) == !(xor (xor g j1) j2))=w) :
    xor (xor (xor (xor b g) j1) j2) w=p := by cases p <;> cases b <;> cases g <;> cases j1 <;> cases j2 <;> cases w <;> simp_all

variable (v : α → Bool) (a b c d e u : α)
variable {cn p y w : Bool}

theorem solveOut_eval (hy : y=xor p ((base a b c d e u cn).eval v)) (obs : y=w) :
    (solveOut a b c d e u cn w).eval v=p := by
  rw [hy] at obs; exact (eval_flip ..).trans (outAlg _ _ _ obs)

theorem solveHit_eval (y1 y2 : α) (hy : y=xor p ((base a b c d e u cn).eval v))
    (obs : xor (xor y (v y1)) (v y2)=w) : (solveHit a b c d e u y1 y2 cn w).eval v=p := by
  rw [hy] at obs; exact (eval_flip ..).trans (hitAlg _ _ _ _ _ obs)

theorem solveTwo_eval (s3 u3 : α) (c3 : Bool) (hy : y=xor p ((base a b c d e u cn).eval v))
    (obs : (y == (inj s3 u3 c3).eval v)=w) : (solveTwo a b c d e u s3 u3 cn c3 w).eval v=p := by
  rw [hy] at obs; exact (eval_flip ..).trans (twoAlg _ _ _ _ obs)

theorem solveOne_eval (s1 u1 s2 u2 : α) (c1 c2 : Bool) (hy : y=xor p ((base a b c d e u cn).eval v))
    (obs : (y == !(xor (xor (xor (xor (v b) (v c)) (v d)) ((inj s1 u1 c1).eval v)) ((inj s2 u2 c2).eval v)))=w) :
    (solveOne a b c d e u s1 u1 s2 u2 cn c1 c2 w).eval v=p := by
  rw [hy] at obs; exact (eval_flip ..).trans (oneAlg _ _ _ _ _ _ obs)

end PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram.Local

namespace PEqualNP.Outside.L_meta_25571_aux.Grid
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
variable {k : Nat} (P : Params k) (c : Nat → Row k) (f : Row k → Nat → Bool)
noncomputable abbrev V {j : Nat} (u : Row k) : Ref k j → Bool := fun a => env (rowCtx k) (node P c f) a u

structure BasePins (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  row : α
  cn : Bool

def BasePins.expr {α : Type} (b : BasePins α) := Local.base b.a b.b b.c b.d b.e b.row b.cn

theorem basePins {J s z : Nat} (hz : Active P (s+1) z) (hs : 3≤s) (hj : Slot P 0 (e (s+1) z) ≤ J) :
    ∃ b : BasePins (Ref k J),
      (∀ u, val c f (s+1) z u = xor (f u (e (s+1) z)) (b.expr.eval (V P c f u))) ∧
      ∀ u, xor (xor (V P c f u b.b) (V P c f u b.c)) (V P c f u b.d) = Line.lGuard u c (f u) s (z+2) := by
  let ref (y : Nat) (lo : z-1≤y) (hi : y≤z+3) := prevRef P (j:=J) s y (lt_of_lt_of_le (predBeforeProbe hz hs lo hi) hj)
  let p : BasePins (Ref k J) := ⟨ref (z-1) (by omega) (by omega), ref z (by omega) (by omega),
    ref (z+1) (by omega) (by omega),ref (z+2) (by omega) (by omega),ref (z+3) (by omega) (by omega),
    rowRef P (e (s+1) z),(c (s+1)).val.testBit (z%k)⟩
  have refEq (u : Row k) (y) (lo : z-1≤y) (hi : y≤z+3) : V P c f u (ref y lo hi) = val c f s y u :=
    prevEval P c f (predActive hz lo hi) _ u
  refine ⟨p,?_,?_⟩
  · intro u
    have iPos := injDiag (z:=z) (show 2≤s by omega)
    simp only [p,BasePins.expr,Local.base,Local.eval_flip,Local.core,Local.tr,Expr.eval,Op.eval,refEq,V,rowEval]
    unfold val
    rw [Line.lineStep_succ]
    change _ = _
    rw [←iPos];unfold injPos
    simp only [Bool.xor_comm, Bool.xor_left_comm, Bool.xor_assoc]
  · intro u
    simp only [p,refEq,val,Line.lGuard,Nat.add_sub_cancel,show z+2-1=z+1 by omega]

end PEqualNP.Outside.L_meta_25571_aux.Grid

namespace PEqualNP.Outside.L_meta_25571_aux.Grid
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
variable {k : Nat} (P : Params k) (c : Nat → Row k) (f : Row k → Nat → Bool)

theorem injPins {j b d : Nat} (hj : j<P.a) (hb : b<3) (d1 : 1≤d) (d2 : d≤2) :
    let J := Slot P 0 (P.pp (3*j+b))
    ∃ s uR : Ref k J, ∃ cn : Bool, ∀ u : Row k,
      (Local.inj s uR cn).eval (V P c f u) = Line.lInj u c (f u) (time j) (stop P j+d) := by
  intro J
  let y := stop P j+d+3-2*time j
  obtain ⟨ac,lt⟩ := extInj P hj hb d1 d2
  let s := prevRef P (j:=J) 0 y lt
  let uR := rowRef P (j:=J) y
  let cn := (c (time j)).val.testBit ((stop P j+d)%k)
  refine ⟨s,uR,cn,fun u => ?_⟩
  have eqs : V P c f u s = f u y := prevEval P c f ac _ u
  have equ : V P c f u uR=u.val.testBit (y%k) := rowEval P c f y u
  simp only [Local.inj,Local.eval_flip,Expr.eval,Op.eval,eqs,equ]
  rfl

end PEqualNP.Outside.L_meta_25571_aux.Grid

namespace PEqualNP.Outside.L_meta_25571_aux.Grid
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Scan (summary)
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
variable {k : Nat} (P : Params k) (c : Nat → Row k) (f : Row k → Nat → Bool)

theorem probeBase {j b : Nat} (hj : j<P.a) (hb : b<3) :
    let J:=Slot P 0 (P.pp (3*j+b))
    ∃ t : BasePins (Ref k J),
      (∀ u, val c f (time j) (col P j b) u = xor (f u (P.pp (3*j+b))) (t.expr.eval (V P c f u))) ∧
      ∀ u, xor (xor (V P c f u t.b) (V P c f u t.c)) (V P c f u t.d) =
        Line.lGuard u c (f u) (tick j-2) (col P j b+2) := by
  intro J
  have tm : tick j-2+1=time j := by unfold time tick; omega
  have ac := probeActive P j b hj hb
  have rk:=probeRank P j b hj hb
  rw [←tm] at ac rk
  obtain ⟨t,h,g⟩ := basePins P c f (J:=J) ac (by unfold tick;omega) (by rw [rk])
  rw [rk,tm] at h
  exact ⟨t,h,g⟩

theorem canOne (j : Nat) (hj : j<P.a) (hq : ∀ u, lineOne u c (f u) ((summary P.v j).1) (tick j) (stop P j)=P.v.testBit (3*j)) :
    Can P c f (Slot P 0 (P.pp (3*j+0))) (fun u => f u (P.pp (3*j+0))) := by
  let want := P.v.testBit (3*j)
  by_cases hmode : (summary P.v j).1=1
  · obtain ⟨t,hy,old⟩ := probeBase P c f hj (by decide : 0<3)
    obtain ⟨s1,u1,c1,h1⟩ := injPins P c f (b:=0) (d:=1) hj (by decide) (by decide) (by decide)
    obtain ⟨s2,u2,c2,h2⟩ := injPins P c f (b:=0) (d:=2) hj (by decide) (by decide) (by decide)
    refine ⟨Local.solveOne t.a t.b t.c t.d t.e t.row s1 u1 s2 u2 t.cn c1 c2 want,le_trans (Local.solveOne_cost ..) (by decide),?_⟩
    intro u
    apply Local.solveOne_eval (V P c f u) t.a t.b t.c t.d t.e t.row s1 u1 s2 u2 c1 c2 (hy u)
    rw [old u,h1 u,h2 u]
    simpa only [lineOne,hmode,beq_self_eq_true,ite_true,col,Nat.sub_zero,val,time,want] using hq u
  · refine ⟨.lit want,by change 1≤72;decide,?_⟩
    intro u
    have hw:=hq u
    have idx : P.pp (3*j+0) = stop P j+3-2*tick j+2 := by simp only [Params.pp,show (3*j+0)/3=j by omega,show (3*j+0)%3=0 by omega,Nat.sub_zero];rfl
    rw [idx]; exact (by simpa [Expr.eval,lineOne,hmode,want] using hw.symm)

theorem canTwo (j : Nat) (hj : j<P.a) (hq : ∀ u, lineTwo u c (f u) ((summary P.v j).1) (tick j) (stop P j)=P.v.testBit (3*j+1)) :
    Can P c f (Slot P 0 (P.pp (3*j+1))) (fun u => f u (P.pp (3*j+1))) := by
  let want := P.v.testBit (3*j+1)
  by_cases hmode : (summary P.v j).1=0
  · refine ⟨.lit want,by change 1≤72;decide,?_⟩
    intro u
    have hw:=hq u
    have idx : P.pp (3*j+1) = stop P j+3-2*tick j+1 := by simp only [Params.pp,show (3*j+1)/3=j by omega,show (3*j+1)%3=1 by omega];unfold left stop;omega
    rw [idx]; exact (by simpa [Expr.eval,lineTwo,hmode,want] using hw.symm)
  · obtain ⟨t,hy,_⟩ := probeBase P c f hj (by decide : 1<3)
    obtain ⟨s2,u2,c2,h2⟩ := injPins P c f (b:=1) (d:=2) hj (by decide) (by decide) (by decide)
    refine ⟨Local.solveTwo t.a t.b t.c t.d t.e t.row s2 u2 t.cn c2 want,le_trans (Local.solveTwo_cost ..) (by decide),?_⟩
    intro u
    apply Local.solveTwo_eval (V P c f u) t.a t.b t.c t.d t.e t.row s2 u2 c2 (hy u)
    rw [h2 u]
    simpa [lineTwo,hmode,col,val,time,want] using hq u

end PEqualNP.Outside.L_meta_25571_aux.Grid

namespace PEqualNP.Outside.L_meta_25571_aux.Grid
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
variable {k : Nat} (P : Params k) (c : Nat → Row k) (seed : Row k) (target : Fin (2^Semantics.M P))

theorem canTerminal {j : Nat} (hj : j<Semantics.M P) :
    Can P c (Semantics.cutSource P c seed target) (Slot P 0 (A P+j)) (fun u => (Semantics.cutSource P c seed target) u (A P+j)) := by
  obtain ⟨ac,eq⟩ := targetActive P hj
  have hr:=P.hr
  have tim : P.r-1+1=P.r := by omega
  rw [←tim] at ac eq
  obtain ⟨p,hy,_⟩:=basePins P c (Semantics.cutSource P c seed target) ac (by omega) (by rw [eq])
  refine ⟨Local.solveOut p.a p.b p.c p.d p.e p.row p.cn (target.val.testBit j), (Local.solveOut_cost ..).trans (by decide),fun u => ?_⟩
  have obs:=Semantics.cutTerminal P c seed target u j hj
  have hh:=hy u
  rw [eq,tim] at hh
  exact Local.solveOut_eval _ _ _ _ _ _ _ hh obs

theorem canHit {j : Nat} (hj:j<P.a) :
    Can P c (Semantics.cutSource P c seed target) (Slot P 0 (P.pp (3*j+2))) (fun u => (Semantics.cutSource P c seed target) u (P.pp (3*j+2))) := by
  have t : tick j-2+1=time j := by unfold time tick;omega
  have ac:=probeActive P j 2 hj (by decide)
  have eq:=probeRank P j 2 hj (by decide)
  rw [←t] at ac eq
  obtain ⟨p,hy,_⟩:=basePins P c (Semantics.cutSource P c seed target) ac (by unfold tick;omega) (by rw [eq])
  obtain ⟨ac1,lt1⟩:=hitExtra P (b:=1) hj (by decide)
  obtain ⟨ac0,lt0⟩:=hitExtra P (b:=0) hj (by decide)
  let a1:=prevRef P (time j) (col P j 1) lt1
  let a0:=prevRef P (time j) (col P j 0) lt0
  let want:=P.v.testBit (3*j+2)
  refine ⟨Local.solveHit p.a p.b p.c p.d p.e p.row a1 a0 p.cn want,(Local.solveHit_cost ..).trans (by decide),fun u => ?_⟩
  have hh:=hy u
  rw [eq,t] at hh
  apply Local.solveHit_eval _ _ _ _ _ _ _ _ _ hh
  have ev1 : V P c (Semantics.cutSource P c seed target) u a1=val c (Semantics.cutSource P c seed target) (time j) (col P j 1) u := prevEval P c (Semantics.cutSource P c seed target) ac1 lt1 u
  have ev0 : V P c (Semantics.cutSource P c seed target) u a0=val c (Semantics.cutSource P c seed target) (time j) (col P j 0) u := prevEval P c (Semantics.cutSource P c seed target) ac0 lt0 u
  rw [ev1,ev0]
  exact (Semantics.cutTranscript P c seed target u j hj).2.2
end PEqualNP.Outside.L_meta_25571_aux.Grid

namespace PEqualNP.Outside.L_meta_25571_aux.Grid
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
variable {k : Nat} (P : Params k) (c : Nat → Row k) (f : Row k → Nat → Bool)
abbrev CanAt (z : Nat) := Can P c f (Slot P 0 z) (fun u => f u z)
lemma canAtConst (z : Nat) (b : Bool) (h : ∀ u, f u z=b) : CanAt P c f z :=
  ⟨.lit b,by change 1≤72;decide,fun u => (h u).symm⟩
lemma classifyBase (seed : Row k)
    (outside : ∀ z, P.q≤z → ∀ u, f u z=false)
    (seeded : ∀ z, z<P.q → pivotBit P (z%k)=false → ∀ u, f u z=seed.val.testBit (z%k))
    (one : ∀ j<P.a, CanAt P c f (P.pp (3*j)))
    (two : ∀ j<P.a, CanAt P c f (P.pp (3*j+1)))
    (hit : ∀ j<P.a, CanAt P c f (P.pp (3*j+2)))
    (out : ∀ j<width P, CanAt P c f (A P+j)) :
    ∀ z, Active P 0 z → CanAt P c f z := by
  intro z ac
  have lo:A P≤z := by have hz:=ac.2.1;omega
  by_cases cut:z<P.q
  · let b : Fin k := ⟨z%k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
    by_cases on : pivotBit P b.val=true
    · obtain (⟨n,he⟩|⟨j,he⟩) := (pivotSpec P b).mp on
      · have hval : P.pp n.val % k = z%k := congrArg Fin.val he
        have pos := P.sameMod (P.interval n.isLt).1 (P.interval n.isLt).2 lo cut hval
        rw [←pos]
        let j := n.val / 3
        have hj:j<P.a := by have hn:=n.isLt;change n.val<3*P.a at hn;dsimp [j];omega
        rcases (show n.val=3*j ∨ n.val=3*j+1 ∨ n.val=3*j+2 by dsimp [j];omega) with h|h|h
        · rw [h];exact one _ hj
        · rw [h];exact two _ hj
        · rw [h];exact hit _ hj
      · have hval : (P.q+j.val)%k=z%k := congrArg Fin.val he
        rw [shifted] at hval
        have qk:=qge P;have wk:=width_le P;have jl:=j.isLt
        have pos:=P.sameMod (by omega : P.q-k≤P.q-k+j.val) (by omega) lo cut hval
        exact pos ▸ out j.val jl
    · exact canAtConst P c f z _ (seeded z cut (Bool.eq_false_iff.mpr on))
  · exact canAtConst P c f z false (outside z (by omega))
lemma semanticBase (seed : Row k) (target : Fin (2^width P)) :
    let f:=Semantics.cutSource P c seed target
    (∀ j<P.a, CanAt P c f (P.pp (3*j))) →
    (∀ j<P.a, CanAt P c f (P.pp (3*j+1))) →
    (∀ j<P.a, CanAt P c f (P.pp (3*j+2))) →
    (∀ j<width P, CanAt P c f (A P+j)) →
    ∀ z, Active P 0 z → CanAt P c f z := by
  intro f one two hit out
  apply classifyBase P c f seed _ _ one two hit out
  · intro z hz u
    simp [f,Semantics.cutSource,Line.cut,Nat.not_lt_of_ge hz]
  · intro z hz np u
    have h:=Semantics.nonpivotSource P c seed target u ⟨z%k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩ np
    simpa only [f,Semantics.cutSource,Line.cut,ite_eq_left hz,Word.word39] using h
end PEqualNP.Outside.L_meta_25571_aux.Grid

namespace PEqualNP.Outside.L_meta_25571_aux.Assemble
open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Word (src word39)
open PEqualNP.Outside.L_meta_25545_aux.Word.Layout (inputWord)
open PEqualNP.Outside.L_meta_25571_aux.Rank
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_25571_aux.BoundedDiagram
variable {k : Nat} (P : Params k)
lemma chooseLift (b : Fin k) : ∃ z : Nat, P.q-k ≤ z ∧ z < P.q ∧ z % k = b.val := by
  have qk : k≤P.q := by have := P.hd; unfold Params.q; omega
  let shift : Fin k → Fin k := fun d => ⟨(P.q-k+d.val)%k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
  have inj : Function.Injective shift := by
    intro x y eq
    have hx:=x.isLt; have hy:=y.isLt
    have e := P.sameMod (x:=P.q-k+x.val) (y:=P.q-k+y.val) (by omega) (by omega) (by omega) (by omega) (congrArg Fin.val eq)
    exact Fin.ext (by omega)
  obtain ⟨d,hd⟩ := (Finite.injective_iff_surjective.mp inj) b
  exact ⟨P.q-k+d.val,by omega,by have:=d.isLt;omega,congrArg Fin.val hd⟩
lemma realized (c : Nat → Fin (2^k)) (seed : Fin (2^k)) (target : Fin (2^width P))
    (base : ∀ z, Active P 0 z → Grid.Can P c (Semantics.cutSource P c seed target) (Slot P 0 z) (fun u => Semantics.cutSource P c seed target u z)) :
    ∃ D : Circuit, Valid k D ∧ D.size ≤ 128*(k+1)*(P.r+1) ∧
      ∃ w : Fin k → Fin (k+D.size), ∀ u i,
        (D.wires ((rowCtx k).inputs u)).getD (w i).val false = (Semantics.getKey P c seed target u).val.testBit i.val := by
  let key := Semantics.getKey P c seed target
  let x (u : Fin (2^k)) : Fin (2^k) := ⟨src u (key u).val,Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) u.isLt⟩
  obtain ⟨C,vc,lim,avail⟩ := Grid.build P c (Semantics.cutSource P c seed target) base
  have ready (i : Fin k) : Available (rowCtx k) C (fun u => (x u).val.testBit i.val) := by
    obtain ⟨z,lo,hi,eq⟩ := chooseLift P i
    have act : Active P 0 z := by change 0≤P.r ∧ P.q-k+0≤z ∧ z+0≤P.q+3*P.r;omega
    have h := avail 0 z act
    have ident : Grid.val c (Semantics.cutSource P c seed target) 0 z = fun u => (x u).val.testBit i.val := by
      funext u; change (Line.cut P.q (word39 u (key u)) z) = _
      simp only [Line.cut,ite_eq_left hi,word39,eq];rfl
    rwa [ident] at h
  obtain ⟨D,vd,sz,w,hw⟩ := exposeRaw vc x ready
  refine ⟨D,vd,?_,w,?_⟩
  · rw [sz];exact (Nat.add_le_add_right lim _).trans (Local.budget72 P.hr P.hkd P.hd)
  · intro u i
    have eq : inputWord u (x u) = key u := Fin.ext (P.keyRecover u (key u))
    exact (hw u i).trans (congrArg (fun (w : Fin (2^k)) => w.val.testBit i.val) eq)
end PEqualNP.Outside.L_meta_25571_aux.Assemble

open PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25571_aux
theorem PEqualNP.Outside.L_meta_25571 : (∀ (k r d i : Nat), 6 ≤ r → k + 3 + d = 5 * r →
  let attempts := r - 5
  d ≤ attempts → i < k → i + (2 * attempts - d) ≤ k →
  ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  let guard := fun (row round key stop : Nat) =>
    xor (xor (bit row round key (stop - 2)) (bit row round key (stop - 1))) (bit row round key stop)
  let move := fun (mode letter : Nat) =>
    let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)
    let hit := letter.testBit 2
    (if aligned then (if hit then 0 else 2) else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (0, 0)
  let q := k + i + 3 * r - d
  let trace := fun (row key length : Nat) =>
    ((List.range length).foldl (fun (st : Nat × Nat × Nat) idx =>
      let t := 5 + idx
      let edge := q - 13 - 3 * idx + st.2.1
      let left := edge + 3 - 2 * t
      let x := rot 1 key ^^^ row
      let v := injected (t - 1) key (edge + 2)
      let oldMix := guard row (t - 2) key (edge + 2)
      let uBit := xor oldMix (injected (t - 1) key (edge + 1))
      let one := if st.1 == 1 then
        bit row (t - 1) key edge == !(xor uBit v)
        else x.testBit ((left + 2) % k)
      let two := if st.1 == 0 then x.testBit ((left + 1) % k)
        else bit row (t - 1) key (edge - 1) == v
      let hit := guard row (t - 1) key edge
      let digit := one.toNat + 2 * two.toNat + 4 * hit.toNat
      let outcome := move st.1 digit
      (outcome.1, st.2.1 + outcome.2, st.2.2 ||| (digit <<< (3 * idx)))) (0, 0, 0)).2.2
  ∀ (a : Nat) (code : Fin (8 ^ a)), a ≤ attempts →
    (a = 0 ∨ d < (summary code.val (a - 1)).2 + 2 * (attempts + 1 - a)) →
    let m := if a = attempts then (summary code.val a).2 - d else 0
    let pivot := fun (candidate : Nat) =>
      (List.range a).any (fun digitIndex =>
        let priorGain := (summary code.val digitIndex).2
        let roundNo := 5 + digitIndex
        let pivotLeft := q - 13 - 3 * digitIndex + priorGain + 3 - 2 * roundNo
        (List.range 3).any (fun offset => (pivotLeft + offset) % k == candidate)) ||
      (List.range m).any (fun outPos => (q + outPos) % k == candidate)
    ((List.range k).filter (fun cellIndex => !(pivot cellIndex))).length = k - 3 * a - m ∧
      ∀ (seed : Fin (2 ^ k)) (target : Fin (2 ^ m)),
      ∃ (getKey : Fin (2 ^ k) → Fin (2 ^ k)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (wire : Fin k → Fin (k + C.size)),
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack k C ∧
        C.size ≤ 128 * (k + 1) * (r + 1) ∧
        (∀ rowName rawKey : Fin (2 ^ k), rawKey = getKey rowName ↔
          trace rowName.val rawKey.val a = code.val ∧
          (∀ pos : Fin k, pivot pos.val = false →
            (rot 1 rawKey.val ^^^ rowName.val).testBit pos.val = seed.val.testBit pos.val) ∧
          (state rowName.val r rawKey.val >>> i) % 2 ^ m = target.val) ∧
        ∀ (rowName : Fin (2 ^ k)) (outBit : Fin k),
          let inputs := (List.range k).map (fun inputBit => rowName.val.testBit inputBit)
          (C.wires inputs).getD (wire outBit).val false = (getKey rowName).val.testBit outBit.val) := by
  intro k r d i hr hkd attempts hd hi him c rot step state injected bit guard move summary q trace a code ha eligible m pivot
  let P : Params k := ⟨r,d,i,a,code.val,hr,hkd,hd,hi,him,ha,code.isLt,eligible⟩
  refine ⟨freeCard P,?_⟩
  intro seed target
  let f := Semantics.cutSource P c seed target
  have base := Grid.semanticBase P c seed target
    (fun j hj => Grid.canOne P c f j hj (fun u => (Semantics.cutTranscript P c seed target u j hj).1))
    (fun j hj => Grid.canTwo P c f j hj (fun u => (Semantics.cutTranscript P c seed target u j hj).2.1))
    (fun j hj => Grid.canHit P c seed target hj)
    (fun j hj => Grid.canTerminal P c seed target hj)
  obtain ⟨D,vd,size,w,hw⟩ := Assemble.realized P c seed target base
  exact ⟨Semantics.getKey P c seed target,D,w,vd.fan,vd.back,size,Semantics.getKeySpec P c seed target,hw⟩
