import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25561_aux
def offsets61 : Finset Nat := {0,1,4,6}
def G61 {n : Nat} (u v : Fin n) := decide ((v.val+n-u.val)%n∈offsets61)
lemma wrap61 {n x:Nat} (h:x<2*n) : x%n=if x<n then x else x-n := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
def ref61 {n:Nat} (hn:13≤n) (i:Fin n) : Fin n :=
  ⟨(n+1-i.val)%n,Nat.mod_lt _ (by omega)⟩
lemma refVal61 {n:Nat} (hn:13≤n) (i:Fin n) : (ref61 hn i).val=if i.val≤1 then 1-i.val else n+1-i.val := by
  change (n+1-i.val)%n=_
  rw [wrap61 (by omega)]
  have:=i.isLt;split_ifs <;> omega
lemma refInvol61 {n:Nat} (hn:13≤n) (i:Fin n) : ref61 hn (ref61 hn i)=i := by
  apply Fin.ext
  rw [refVal61,refVal61]
  have:=i.isLt;split_ifs <;> omega
def mate61 {n:Nat} (hn:13≤n) : Equiv.Perm (Fin n) :=
  ⟨ref61 hn, ref61 hn, refInvol61 hn, refInvol61 hn⟩
def fixed61 {n:Nat} (hn:13≤n) := Finset.univ.filter (fun i:Fin n=>G61 i (mate61 hn i)=true)
def pairs61 {n:Nat} (hn:13≤n) := Finset.univ.filter (fun p:Fin n × Fin n=>p.1<p.2 ∧ G61 p.1 (mate61 hn p.2)=true)
def sums61 (n z e:Nat) := z+e=1 ∨ z+e=n+1 ∨ z+e=2*n+1
lemma crossIff61 {n:Nat} (hn:13≤n) (i j:Fin n) :
  G61 i (mate61 hn j)=true ↔ sums61 n (i.val+j.val) 0 ∨ sums61 n (i.val+j.val) 1 ∨
    sums61 n (i.val+j.val) 4 ∨ sums61 n (i.val+j.val) 6 := by
  have bi:=i.isLt;have bj:=j.isLt
  have bound: (ref61 hn j).val+n-i.val<2*n := by have:=(ref61 hn j).isLt;omega
  change (decide (((ref61 hn j).val+n-i.val)%n∈offsets61)=true) ↔ _
  rw [decide_eq_true_eq,wrap61 bound,refVal61]
  simp only [offsets61,Finset.mem_insert,Finset.mem_singleton,sums61]
  split_ifs <;> omega
lemma crossSymm61 {n:Nat} (hn:13≤n) (i j:Fin n) :
    G61 i (mate61 hn j)=G61 j (mate61 hn i) := by
  apply Bool.eq_iff_iff.mpr
  rw [crossIff61,crossIff61,Nat.add_comm i.val j.val]
end PEqualNP.Outside.L_meta_25561_aux

namespace PEqualNP.Outside.L_meta_25561_aux
private def dif61 {n : Nat} (u v : Fin n) := (v.val+n-u.val)%n
private theorem colInjD61 {n} (hn : 13≤n) (u : Fin n) {v w : Fin n}
    (h : dif61 u v = dif61 u w) : v=w := by
  apply Fin.ext
  dsimp only [dif61] at h
  rw [wrap61 (by omega),wrap61 (by omega)] at h
  split_ifs at h <;> omega
private theorem rowInjD61 {n} (hn : 13≤n) (v : Fin n) {u w : Fin n}
    (h : dif61 u v = dif61 w v) : u=w := by
  apply Fin.ext
  dsimp only [dif61] at h
  rw [wrap61 (by omega),wrap61 (by omega)] at h
  split_ifs at h <;> omega

theorem noFour61 {n : Nat} (hn : 13≤n) (u v x y : Fin n) (uv : u≠v)
    (ux : G61 u x=true) (vx : G61 v x=true) (uy : G61 u y=true) (vy : G61 v y=true) : x=y := by
  let a := dif61 u x
  let b := dif61 v x
  let c := dif61 u y
  let d := dif61 v y
  have val {i j : Fin n} (e : G61 i j=true) : dif61 i j∈offsets61 := of_decide_eq_true e
  have bd {z : Nat} (m : z∈offsets61) : z<7 := by simp [offsets61] at m;omega
  have ha := bd (val ux)
  have hb := bd (val vx)
  have hc := bd (val uy)
  have hd := bd (val vy)
  have eq : (a+d)%n=(b+c)%n := by
    dsimp [a,b,c,d,dif61]
    rw [←Nat.add_mod,←Nat.add_mod]
    congr 1 <;> omega
  have ea : a+d < n := by dsimp only [a,d];omega
  have eb : b+c < n := by dsimp only [b,c];omega
  rw [Nat.mod_eq_of_lt ea,Nat.mod_eq_of_lt eb] at eq
  have arith : ∀ a b c d : Fin 7, a.val∈offsets61 → b.val∈offsets61 → c.val∈offsets61 →
      d.val∈offsets61 → a.val≠b.val → a.val+d.val=b.val+c.val → a.val=c.val := by decide +kernel
  exact colInjD61 hn u (arith ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩ (val ux) (val vx) (val uy) (val vy)
    (fun e => uv (rowInjD61 hn x e)) eq)

theorem sep61 {α : Type} [Fintype α] [DecidableEq α] (f g : α→Bool)
    (h1 : (Finset.univ.filter (fun x => f x=true)).card=4)
    (h2 : (Finset.univ.filter (fun x => g x=true)).card=4)
    (uniq : ∀ x y, f x=true → g x=true → f y=true → g y=true → x=y) :
    6≤(Finset.univ.filter (fun x => f x≠g x)).card := by
  classical
  let S := Finset.univ.filter (fun x => f x=true)
  let T := Finset.univ.filter (fun x => g x=true)
  have both : (S∩T).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have a := Finset.mem_inter.mp hx
    have b := Finset.mem_inter.mp hy
    exact uniq x y (Finset.mem_filter.mp a.1).2 (Finset.mem_filter.mp a.2).2
      (Finset.mem_filter.mp b.1).2 (Finset.mem_filter.mp b.2).2
  have dis : Disjoint (S\T) (T\S) := by
    exact Finset.disjoint_left.mpr (fun z hz ht => (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp ht).1)
  have sub : (S\T) ∪ (T\S) ⊆ Finset.univ.filter (fun x => f x≠g x) := by
    intro j hj
    rcases Finset.mem_union.mp hj with h|h
    · simpa [S,T] using (show f j≠g j from by
        obtain ⟨a,b⟩ := Finset.mem_sdiff.mp h
        simp [S,T] at a b
        simp [a,b])
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      obtain ⟨a,b⟩ := Finset.mem_sdiff.mp h
      simp [S,T] at a b
      simp [a,b]
  have bound := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at bound
  have a := Finset.card_sdiff_add_card_inter S T
  have b := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at b
  change S.card=4 at h1
  change T.card=4 at h2
  omega

theorem noMon61 {n : Nat} (hn : 13≤n) :
    ¬ ∃ accept : Finset (Fin n) → Prop, (∀ S T,S⊆T → accept S → accept T) ∧
      ∀ u v : Fin n, accept (Finset.univ.filter (fun z : Fin n => z=u ∨ (mate61 hn z).val=v.val)) ↔
        G61 u v=true := by
  rintro ⟨acc,mono,ok⟩
  let z : Fin n := ⟨0,by omega⟩
  let p : Fin n := ⟨2,by omega⟩
  let v := mate61 hn z
  let w := mate61 hn p
  have ev : v.val=1 := by change (ref61 hn z).val=1; simp [refVal61,z]
  have ew : w.val=n-1 := by change (ref61 hn p).val=n-1; simp [refVal61,p]
  have yy : G61 z v=true := by simp [G61,offsets61,z,ev, Nat.mod_eq_of_lt (show 1<n by omega)]
  have nn : G61 z w=false := by simp [G61,offsets61,z,ew, Nat.mod_eq_of_lt (show n-1<n by omega)];omega
  have slim : (Finset.univ.filter (fun i : Fin n => i=z ∨ (mate61 hn i).val=v.val)) ⊆
      Finset.univ.filter (fun i : Fin n => i=z ∨ (mate61 hn i).val=w.val) := by
    intro i hi
    obtain h|h := (Finset.mem_filter.mp hi).2
    · simp [h]
    · have iz := (mate61 hn).injective (show mate61 hn i=mate61 hn z from Fin.ext h)
      simp [iz]
  exact Bool.noConfusion (nn.symm.trans ((ok z w).mp (mono _ _ slim ((ok z v).mpr yy))))
end PEqualNP.Outside.L_meta_25561_aux

namespace PEqualNP.Outside.L_meta_25561_aux
lemma degree61 {n:Nat} (hn:13≤n) (u:Fin n) :
    (Finset.univ.filter (fun v:Fin n=>G61 u v=true)).card=4 := by
  classical
  let S:=Finset.univ.filter (fun v:Fin n=>G61 u v=true)
  let delta:=fun v:Fin n=>(v.val+n-u.val)%n
  have hu:=u.isLt
  have back (v:Fin n) : (delta v+u.val)%n=v.val := by
    dsimp [delta]
    rw [Nat.mod_add_mod,show v.val+n-u.val+u.val=v.val+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt v.isLt]
  have inj:Function.Injective delta := by
    intro v w h;apply Fin.ext;rw [←back v,h,back]
  have m (v:Fin n) : v∈S ↔ delta v∈offsets61 := by simp [S,G61,delta]
  have eq:S.image delta=offsets61 := by
    ext e;constructor
    · intro h;obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp h;exact (m _).1 hv
    · intro h
      have el:e<n:=by simp only [offsets61,Finset.mem_insert,Finset.mem_singleton] at h;omega
      let v:Fin n:=⟨(u.val+e)%n,Nat.mod_lt _ (by omega)⟩
      have de:delta v=e := by
        change (((u.val+e)%n+n-u.val)%n)=e
        rw [wrap61 (x:=(u.val+e)%n+n-u.val) (by have := v.isLt;change (u.val+e)%n<n at this;omega),
          wrap61 (x:=u.val+e) (by omega)]
        split_ifs <;> omega
      exact Finset.mem_image.mpr ⟨v,(m v).2 (de ▸ h),de⟩
  change S.card=4
  rw [←Finset.card_image_of_injective S inj,eq]
  decide

private lemma crossDegree61 {n:Nat} (hn:13≤n) (u:Fin n) :
    (Finset.univ.filter (fun v:Fin n=>G61 u (mate61 hn v)=true)).card=4 := by
  let A:=Finset.univ.filter (fun v:Fin n=>G61 u (mate61 hn v)=true)
  have eq:A.image (mate61 hn)=Finset.univ.filter (fun v:Fin n=>G61 u v=true) := by
    ext v;constructor
    · intro h;obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩
    · intro h
      have inv:mate61 hn (mate61 hn v)=v:=refInvol61 hn v
      refine Finset.mem_image.mpr ⟨mate61 hn v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,inv⟩
      rw [inv];exact (Finset.mem_filter.mp h).2
  change A.card=4
  rw [←Finset.card_image_of_injective A (mate61 hn).injective,eq,degree61 hn]

lemma pricePairs61 {n:Nat} (hn:13≤n) : 2*(pairs61 hn).card+(fixed61 hn).card=4*n := by
  classical
  let D:=Finset.univ.filter (fun p:Fin n × Fin n=>G61 p.1 (mate61 hn p.2)=true)
  let U:=pairs61 hn
  let L:=U.image Prod.swap
  let F:=(fixed61 hn).image (fun a=>(a,a))
  have deg:D.card=4*n := by
    calc
      D.card = ∑a:Fin n, ∑b:Fin n, if G61 a (mate61 hn b)=true then 1 else 0 := by
        dsimp [D];rw [Finset.card_filter,Fintype.sum_prod_type]
      _ = ∑_a:Fin n,4 := by
        apply Finset.sum_congr rfl
        intro a _;rw [← Finset.card_filter];exact crossDegree61 hn a
      _ = _ := by simp [Nat.mul_comm]
  have um (a b:Fin n) : (a,b)∈U ↔ a<b ∧ G61 a (mate61 hn b)=true := by simp [U,pairs61]
  have lm (a b:Fin n) : (a,b)∈L ↔ b<a ∧ G61 a (mate61 hn b)=true := by
    constructor
    · intro h;obtain ⟨⟨x,y⟩,hs,eq⟩:=Finset.mem_image.mp h
      change (y,x)=(a,b) at eq
      have ya:y=a:=congrArg Prod.fst eq;have xb:x=b:=congrArg Prod.snd eq
      subst a;subst b
      exact ⟨((um x y).mp hs).1,(crossSymm61 hn x y).symm.trans ((um x y).mp hs).2⟩
    · rintro ⟨h,g⟩
      exact Finset.mem_image.mpr ⟨(b,a),(um b a).mpr ⟨h,(crossSymm61 hn b a).trans g⟩,rfl⟩
  have fm (a b:Fin n) : (a,b)∈F ↔ a=b ∧ G61 a (mate61 hn b)=true := by
    constructor
    · intro h;obtain ⟨x,hx,e⟩:=Finset.mem_image.mp h
      cases e; exact ⟨rfl,(Finset.mem_filter.mp hx).2⟩
    · rintro ⟨rfl,h⟩;exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  have total:(U∪L)∪F=D := by
    ext z;obtain ⟨a,b⟩:=z
    simp only [Finset.mem_union,um,lm,fm,D,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ((h|h)|h) <;> exact h.2
    · intro pos
      rcases lt_trichotomy a b with h|h|h
      · exact Or.inl (Or.inl ⟨h,pos⟩)
      · exact Or.inr ⟨h,pos⟩
      · exact Or.inl (Or.inr ⟨h,pos⟩)
  have ul:Disjoint U L := by
    apply Finset.disjoint_left.mpr;rintro ⟨a,b⟩ h k
    exact (lt_asymm ((um _ _).mp h).1) ((lm _ _).mp k).1
  have df:Disjoint (U∪L) F := by
    apply Finset.disjoint_left.mpr;rintro ⟨a,b⟩ h k
    obtain ⟨rfl,_⟩:=(fm _ _).mp k
    rcases Finset.mem_union.mp h with h|h
    · exact (lt_irrefl _ ((um _ _).mp h).1)
    · exact (lt_irrefl _ ((lm _ _).mp h).1)
  have lc:L.card=U.card:=Finset.card_image_of_injective _ Prod.swap_injective
  have fc:F.card=(fixed61 hn).card:=Finset.card_image_of_injective _ (fun _ _ e=>congrArg Prod.fst e)
  rw [←total,Finset.card_union_of_disjoint df,Finset.card_union_of_disjoint ul,lc,fc] at deg
  change 2*U.card+(fixed61 hn).card=4*n
  omega
end PEqualNP.Outside.L_meta_25561_aux

namespace PEqualNP.Outside.L_meta_25561_aux
lemma fixedCard61 {n:Nat} (hn:13≤n) : (fixed61 hn).card=if n%2=1 then 4 else 2 := by
  classical
  let K:=if n%2=1 then ({0,n/2+1,n/2-1,n/2-2}:Finset Nat) else {0,n/2}
  have test (i:Fin n) : i∈fixed61 hn ↔ i.val∈K := by
    simp only [fixed61,Finset.mem_filter,Finset.mem_univ,true_and,crossIff61,K,sums61]
    split <;> simp only [Finset.mem_insert,Finset.mem_singleton] <;> have:=i.isLt <;> omega
  have range (v:Nat) (h:v∈K) : v<n := by
    dsimp [K] at h; split at h <;> simp only [Finset.mem_insert,Finset.mem_singleton] at h <;> omega
  have eq:(fixed61 hn).image Fin.val=K := by
    ext v;constructor
    · intro h;obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp h;exact (test i).mp hi
    · intro h;exact Finset.mem_image.mpr ⟨⟨v,range v h⟩,(test _).mpr h,rfl⟩
  rw [←Finset.card_image_of_injective _ Fin.val_injective,eq]
  dsimp [K];split
  · rw [Finset.card_insert_of_notMem,Finset.card_insert_of_notMem,Finset.card_insert_of_notMem,Finset.card_singleton]
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] <;> omega
  · rw [Finset.card_insert_of_notMem,Finset.card_singleton]
    all_goals simp only [Finset.mem_singleton] <;> omega
lemma lit61_iff {n:Nat} (hn:13≤n) (u v i:Fin n):
    i=u ∨ (mate61 hn i).val=v.val ↔ i∈({u,mate61 hn v}:Finset (Fin n)) := by
  simp only [Finset.mem_insert,Finset.mem_singleton]
  have mir:(mate61 hn i).val=v.val ↔ i=mate61 hn v := by
    constructor
    · intro h;have same:ref61 hn i=v:=Fin.ext h
      exact (refInvol61 hn i).symm.trans (congrArg (ref61 hn) same)
    · intro eq;rw [eq];exact congrArg Fin.val (refInvol61 hn v)
  rw [mir]

lemma decode61 {n:Nat} (hn:13≤n) (u v:Fin n) :
    let S:Finset (Fin n):={u,mate61 hn v}
    G61 u v=true ↔ (∃p∈pairs61 hn,p.1∈S ∧ p.2∈S) ∨
      (S⊆fixed61 hn ∧ ¬∃i∈fixed61 hn,∃j∈fixed61 hn,i≠j ∧ i∈S ∧ j∈S) := by
  classical
  let y:=mate61 hn v
  have inv:(mate61 hn y)=v:=refInvol61 hn v
  let S:Finset (Fin n):={u,y}
  have mem (i:Fin n):i∈S ↔ i=u ∨ i=y := by simp [S]
  have isfix (i:Fin n) : i∈fixed61 hn ↔ G61 i (mate61 hn i)=true := by simp [fixed61]
  change G61 u v=true ↔ (∃p∈pairs61 hn,p.1∈S ∧ p.2∈S) ∨ _
  constructor
  · intro yes
    rcases lt_trichotomy u y with xy|eq|yx
    · left;exact ⟨(u,y),Finset.mem_filter.mpr ⟨Finset.mem_univ _,xy,by simpa [inv] using yes⟩,
        (mem _).mpr (Or.inl rfl),(mem _).mpr (Or.inr rfl)⟩
    · right
      have single:S={u}:=by simp [S,eq]
      change S⊆fixed61 hn ∧ _
      have one:u∈fixed61 hn:=(isfix _).mpr (by simpa only [eq,inv] using (show G61 u v=true from yes))
      constructor
      · rw [single];exact Finset.singleton_subset_iff.mpr one
      · rintro ⟨i,_,j,_,ne,si,sj⟩
        change i∈S at si;change j∈S at sj
        rw [single,Finset.mem_singleton] at si sj
        exact ne (si.trans sj.symm)
    · left;refine ⟨(y,u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,yx,?_⟩,
        (mem _).mpr (Or.inr rfl),(mem _).mpr (Or.inl rfl)⟩
      rw [crossSymm61 hn y u,inv];exact yes
  · rintro (⟨⟨a,b⟩,hp,ah,bh⟩|⟨hs,uniq⟩)
    · obtain ⟨ab,he⟩: a<b ∧ G61 a (mate61 hn b)=true := (Finset.mem_filter.mp hp).2
      rcases (mem a).mp ah with au|ay <;> rcases (mem b).mp bh with bu|by'
      · rw [au,bu] at ab;exact (lt_irrefl _ ab).elim
      · simpa only [au,by',inv] using he
      · rw [ay,bu,crossSymm61 hn y u,inv] at he;exact he
      · rw [ay,by'] at ab;exact (lt_irrefl _ ab).elim
    · have up:u∈S:=(mem _).mpr (Or.inl rfl)
      have yp:y∈S:=(mem _).mpr (Or.inr rfl)
      have eq:u=y:=by by_contra ne;exact uniq ⟨u,hs up,y,hs yp,ne,up,yp⟩
      have ax:=(isfix u).1 (hs up)
      have out:mate61 hn u=v:=eq ▸ inv
      rwa [out] at ax
end PEqualNP.Outside.L_meta_25561_aux


namespace PEqualNP.Outside.L_meta_25561_aux

inductive Expr61 (n : Nat)
  | var (i : Fin n)
  | both (a b : Expr61 n)
  | either (a b : Expr61 n)
  | inv (a : Expr61 n)

def size61 {n} : Expr61 n → Nat
  | .var _ => 0
  | .both a b | .either a b => size61 a + size61 b + 1
  | .inv a => size61 a + 1

def neg61 {n} : Expr61 n → Nat
  | .var _ => 0
  | .both a b | .either a b => neg61 a + neg61 b
  | .inv a => neg61 a + 1

def eval61 {n} (y : Fin n → Bool) : Expr61 n → Bool
  | .var i => y i
  | .both a b => eval61 y a && eval61 y b
  | .either a b => eval61 y a || eval61 y b
  | .inv a => !(eval61 y a)

end PEqualNP.Outside.L_meta_25561_aux

namespace PEqualNP.Outside.L_meta_25561_aux
lemma join61 {n : Nat} {α : Type} [DecidableEq α] (s : Finset α) (hs : s.Nonempty)
    (g : α → Expr61 n) (k : Nat) (sz : ∀i,size61 (g i)=k) (nz : ∀i,neg61 (g i)=0) :
    ∃ e : Expr61 n, size61 e+1=s.card*(k+1) ∧ neg61 e=0 ∧
       ∀ y, eval61 y e=true ↔ ∃ i∈s,eval61 y (g i)=true := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases h:s.Nonempty
    · obtain ⟨x,sx,nx,ex⟩:=ih h
      refine ⟨.either (g i) x,?_,by simp [neg61,nz,nx],?_⟩
      · simp only [size61,sz,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul]
        omega
      · intro y
        simp only [eval61,Bool.or_eq_true,ex,Finset.exists_mem_insert]
    · have z:=Finset.not_nonempty_iff_eq_empty.mp h
      subst s
      exact ⟨g i,by simp [sz],nz i,by simp⟩

def twoHit61 {n : Nat} (F : Finset (Fin n)) (y : Fin n → Bool) :=
  ∃ i ∈ F, ∃ j ∈ F, i≠j ∧ y i=true ∧ y j=true
lemma twoCard61 {n} (F : Finset (Fin n)) (y : Fin n → Bool) :
    twoHit61 F y ↔ 1<(F.filter (fun i=>y i=true)).card := by
  rw [Finset.one_lt_card]
  simp only [twoHit61,Finset.mem_filter]
  grind
def four61 {n} (a b c d : Fin n) : Expr61 n :=
  .either (.either (.both (.var a) (.var b)) (.both (.var c) (.var d)))
    (.both (.either (.var a) (.var b)) (.either (.var c) (.var d)))
lemma threshold61 {n} (F : Finset (Fin n)) (h : F.card=2 ∨ F.card=4) :
    ∃ e : Expr61 n, size61 e=(if F.card=4 then 7 else 1) ∧ neg61 e=0 ∧
      ∀y,eval61 y e=true ↔ twoHit61 F y := by
  classical
  rcases h with h|h
  · obtain ⟨a,b,ne,eq⟩:=Finset.card_eq_two.mp h
    refine ⟨.both (.var a) (.var b),by simp [h,size61],rfl,?_⟩
    intro y
    rw [twoCard61,eq]
    cases ha:y a <;> cases hb:y b <;> simp [eval61,Finset.filter_insert,Finset.filter_singleton,ha,hb,ne]
  · obtain ⟨a,b,c,d,ab,ac,ad,bc,bd,cd,eq⟩:=Finset.card_eq_four.mp h
    refine ⟨four61 a b c d,by simp [h,four61,size61],rfl,?_⟩
    intro y
    rw [twoCard61,eq]
    cases ha:y a <;> cases hb:y b <;> cases hc:y c <;> cases hd:y d <;>
      simp [four61,eval61,Finset.filter_insert,Finset.filter_singleton,ha,hb,hc,hd,ab,ac,ad,bc,bd,cd,
        Finset.card_insert_of_notMem]

lemma tail61 {n} (F : Finset (Fin n)) (P : Finset (Fin n × Fin n))
    (hcard : F.card=2 ∨ F.card=4) (pos : P.Nonempty) (out : Fᶜ.Nonempty) :
    ∃ e : Expr61 n, size61 e+1=2*P.card+(n-F.card)+(if F.card=4 then 7 else 1)+2 ∧ neg61 e=1 ∧
      ∀ (S : Finset (Fin n)), eval61 (fun i=>decide (i∈S)) e=true ↔
        (∃p∈P,p.1∈S ∧ p.2∈S) ∨
        (S⊆F ∧ ¬∃i∈F,∃j∈F,i≠j ∧ i∈S ∧ j∈S) := by
  classical
  obtain ⟨a,sa,na,ea⟩:=join61 P pos (fun p=>.both (.var p.1) (.var p.2)) 1 (fun _=>rfl) (fun _=>rfl)
  obtain ⟨b,sb,nb,eb⟩:=join61 Fᶜ out (fun i=>.var i) 0 (fun _=>rfl) (fun _=>rfl)
  obtain ⟨c,sc,nc,ec⟩:=threshold61 F hcard
  refine ⟨.either a (.inv (.either b c)),?_,by simp [neg61,na,nb,nc],?_⟩
  · simp only [size61,sc]
    simp only [Finset.card_compl,Fintype.card_fin] at sb
    omega
  · intro S
    let y := fun i=>decide (i∈S)
    have ea' : eval61 y a=true ↔ ∃p∈P,p.1∈S ∧ p.2∈S := by
      simpa [y,eval61] using ea y
    have eb' : eval61 y b=true ↔ ∃i, i∉F ∧ i∈S := by
      simpa [y,eval61] using eb y
    have ec' : eval61 y c=true ↔ ∃i∈F,∃j∈F,i≠j ∧ i∈S ∧ j∈S := by
      simpa [y,twoHit61] using ec y
    change (eval61 y a || !(eval61 y b || eval61 y c))=true ↔ _
    rw [(show ∀a b c : Bool, (a || !(b || c))=true ↔ a=true ∨ b≠true ∧ c≠true by decide) (eval61 y a) (eval61 y b) (eval61 y c)]
    simp only [ne_eq,ea',eb',ec']
    have outside : (¬ ∃ i, i ∉ F ∧ i ∈ S) ↔ S ⊆ F := by
      constructor
      · intro h i hi; by_contra c; exact h ⟨i,c,hi⟩
      · rintro h ⟨i,ni,si⟩; exact ni (h si)
    rw [outside]

end PEqualNP.Outside.L_meta_25561_aux


namespace PEqualNP.Outside.L_meta_25561_aux
lemma suffix61 {n : Nat} (hn : 13≤n) :
    ∃ e : Expr61 n, n+size61 e≤(if n%2=1 then 6*n else 6*n-2) ∧ neg61 e=1 ∧
      ∀ u v : Fin n, eval61 (fun i=>decide (i=u ∨ i=v)) e = G61 u (mate61 hn v) := by
  classical
  have cf:=fixedCard61 hn
  have cp:=pricePairs61 hn
  have fs : (fixed61 hn).card=2 ∨ (fixed61 hn).card=4 := by split at cf <;> omega
  have pn : (pairs61 hn).Nonempty := Finset.card_pos.mp (by omega)
  have no : (fixed61 hn)ᶜ.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_compl,Fintype.card_fin];omega)
  obtain ⟨e,sz,ng,yes⟩:=tail61 (fixed61 hn) (pairs61 hn) fs pn no
  refine ⟨e,?_,ng,?_⟩
  · split <;> rename_i h
    · rw [if_pos h] at cf
      rw [if_pos cf] at sz
      omega
    · rw [if_neg h] at cf
      rw [if_neg (by omega)] at sz
      omega
  · intro u v
    apply Bool.eq_iff_iff.mpr
    have d:=decode61 hn u (mate61 hn v)
    have inv : (mate61 hn) ((mate61 hn) v)=v := refInvol61 hn v
    dsimp only at d
    rw [inv] at d
    have y:=yes {u,v}
    simpa only [Finset.mem_insert,Finset.mem_singleton] using (y.trans d.symm)
end PEqualNP.Outside.L_meta_25561_aux


namespace PEqualNP.Outside.L_meta_25561_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
def pairedGate61 {n} (mate : Equiv.Perm (Fin n)) (i : Fin n) : Gate := ⟨.or,[i.val,n+(mate i).val]⟩
def pairedGates61 {n} (mate : Equiv.Perm (Fin n)) := List.ofFn (pairedGate61 mate)
def pairedCircuit61 {n} (mate : Equiv.Perm (Fin n)) : Circuit := ⟨pairedGates61 mate,0⟩
theorem pairSize61 {n} (mate : Equiv.Perm (Fin n)) : (pairedGates61 mate).length=n := by simp [pairedGates61]
theorem pairGateMem61 {n} (mate : Equiv.Perm (Fin n)) (i : Fin n) : pairedGate61 mate i∈pairedGates61 mate := by simp [pairedGates61]
theorem pairFan61 {n} (mate : Equiv.Perm (Fin n)) : FanInTwo (pairedCircuit61 mate) := by
  intro g hg
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
  simp [pairedGate61]
theorem pairReads61 {n} (mate : Equiv.Perm (Fin n)) : ReadsBack (2*n) (pairedCircuit61 mate) := by
  intro j h i hi
  change j<(pairedGates61 mate).length at h
  have jn : j<n := by simpa [pairSize61] using h
  have atg : gateAt (pairedCircuit61 mate) j=pairedGate61 mate ⟨j,jn⟩ := by
    change (pairedGates61 mate).getD j _=_
    rw [List.getD_eq_getElem _ _ h]
    simp [pairedCircuit61,pairedGates61]
  rw [atg] at hi
  have mlt := (mate ⟨j,jn⟩).isLt
  change i∈[j,n+(mate ⟨j,jn⟩).val] at hi
  simp at hi
  omega
theorem pairNot61 {n} (mate : Equiv.Perm (Fin n)) : PEqualNP.NotBracket.notCount (pairedCircuit61 mate)=0 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.filter_eq_nil_iff.mpr ?_]
  · rfl
  · intro g hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
    simp [pairedGate61]

theorem pairCounts61 {n} (mate : Equiv.Perm (Fin n)) (i : Fin n) :
    ((pairedGates61 mate).map (fun g=>g.inputs.count i.val)).sum=1 ∧
    ((pairedGates61 mate).map (fun g=>g.inputs.count (n+i.val))).sum=1 := by
  have row (j : Fin n) : (pairedGate61 mate j).inputs.count i.val = if j=i then 1 else 0 := by
    by_cases e : j=i
    · subst j;simp [pairedGate61,List.count_cons,show n+(mate i).val≠i.val by have :=i.isLt;omega]
    · have ne : j.val≠i.val := fun h=>e (Fin.ext h)
      simp [pairedGate61,List.count_cons,ne,e,show n+(mate j).val≠i.val by have :=i.isLt;omega]
  have col (j : Fin n) : (pairedGate61 mate j).inputs.count (n+i.val) = if j=mate.symm i then 1 else 0 := by
    have ne : j.val≠n+i.val := by have:=j.isLt;omega
    by_cases e : j=mate.symm i
    · subst j;simp [pairedGate61,List.count_cons,ne]
    · have d : (mate j).val≠i.val := fun h=>e (by rw [←Fin.ext h,mate.symm_apply_apply])
      simp [pairedGate61,List.count_cons,ne,d,e]
  constructor
  · simp [pairedGates61,List.map_ofFn,Function.comp_def,row,List.sum_ofFn]
  · simp [pairedGates61,List.map_ofFn,Function.comp_def,col,List.sum_ofFn]

theorem wiresPair61 {n} (mate : Equiv.Perm (Fin n)) (u v : Fin n) (i : Fin n) :
    ((pairedCircuit61 mate).wires (oneEach u v)).getD (2*n+i.val) false =
      (decide (i=u) || decide (mate i=v)) := by
  let x := oneEach u v
  let out := fun j : Fin n => decide (j=u) || decide (mate j=v)
  have len : x.length=2*n := by simp [x,oneEach];omega
  have al (j : Fin n) : x.getD j.val false=decide (j=u) := by
    unfold x oneEach
    rw [List.getD_append _ _ _ _ (by simpa using j.isLt),List.getD_eq_getElem _ _ (by simpa using j.isLt)]
    simp
  have ar (j : Fin n) : x.getD (n+j.val) false=decide (j=v) := by
    unfold x oneEach
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn,Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simpa using j.isLt)]
    simp
  let applyG := fun (w : List Bool) (g : Gate) => w++[g.op.eval (g.inputs.map (fun i=>w.getD i false))]
  have run (l : List (Fin n)) (a : List Bool) :
      (l.map (pairedGate61 mate)).foldl applyG (x++a) = x++(a++l.map out) := by
    induction l generalizing a with
    | nil => simp
    | cons j l ih =>
      have read (k : Nat) (hk : k<2*n) := List.getD_append x a false k (by omega)
      have step : applyG (x++a) (pairedGate61 mate j)=x++(a++[out j]) := by
        simp only [applyG,pairedGate61,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
          id_eq,Bool.or_false,read j.val (by have:=j.isLt;omega),
          read (n+(mate j).val) (by have:=(mate j).isLt;omega),al,ar,out,List.append_assoc]
      simp only [List.map_cons,List.foldl_cons,step,ih,List.append_assoc,List.singleton_append]
  have allg : pairedGates61 mate=(List.finRange n).map (pairedGate61 mate) := List.ofFn_eq_map
  have val : (pairedCircuit61 mate).wires x=x++List.ofFn out := by
    simpa only [pairedCircuit61,Circuit.wires,allg,List.append_nil,List.nil_append,List.ofFn_eq_map] using run (List.finRange n) []
  change ((pairedCircuit61 mate).wires x).getD _ false=out i
  rw [val,List.getD_append_right _ _ _ _ (by omega),len,Nat.add_sub_cancel_left,List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp
end PEqualNP.Outside.L_meta_25561_aux


namespace PEqualNP.Outside.L_meta_25561_aux
open PEqualNP.CircuitLowerBounds

private instance opDec61 : DecidableEq GateOp := lineDegreeGateOpDecEq

def run61 (gs : List Gate) (p : List Bool) := (⟨gs,0⟩ : Circuit).wires p

theorem runAppend61 (a b : List Gate) (p : List Bool) :
    run61 (a++b) p=run61 b (run61 a p) := by simp [run61,Circuit.wires,List.foldl_append]

theorem runExt61 (gs : List Gate) (p : List Bool) : ∃ tail, run61 gs p = p ++ tail ∧ tail.length=gs.length := by
  induction gs generalizing p with
  | nil => exact ⟨[],by simp [run61,Circuit.wires],rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => p.getD i false))
    obtain ⟨t,eq,lt⟩ := ih (p++[v])
    exact ⟨v::t, by simpa [run61,Circuit.wires,v] using eq, by simp [lt]⟩

theorem runSize61 (gs : List Gate) (p : List Bool) : (run61 gs p).length=p.length+gs.length := by
  obtain ⟨_,e,h⟩ := runExt61 gs p
  simp [e,h]

theorem runKeep61 (gs : List Gate) (p : List Bool) (i : Nat) (hi : i<p.length) :
    (run61 gs p).getD i false=p.getD i false := by
  obtain ⟨t,eq,_⟩ := runExt61 gs p
  simp [eq,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

def tick61 (gs : List Gate) := (gs.filter fun g=>decide (g.op=.not)).length

def shape61 (g : Gate) : Prop := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ (g.inputs.length≤2) ∧ (g.op=.not → ∃ w, g.inputs=[w])

def safe61 (lo b : Nat) (gs : List Gate) : Prop := ∀ (j : Nat) (h : j<gs.length),
  shape61 gs[j] ∧ ∀ w∈gs[j].inputs, lo≤w ∧ w<b+j

theorem safeAppend61 {lo b} {a c : List Gate} (ha : safe61 lo b a)
    (hc : safe61 lo (b+a.length) c) : safe61 lo b (a++c) := by
  intro j hj
  by_cases h : j<a.length
  · simpa only [List.getElem_append_left h] using ha j h
  · rw [List.getElem_append_right (by omega)]
    obtain ⟨sh,rd⟩ := hc (j-a.length) (by simpa using (show j-a.length<c.length by simp at hj;omega))
    exact ⟨sh,fun w hw => (rd w hw).imp_right (by intros;omega)⟩

theorem safeOne61 {lo b : Nat} {g : Gate} (h : shape61 g)
    (rd : ∀ w∈g.inputs,lo≤w ∧ w<b) : safe61 lo b [g] := by
  intro j hj
  have eq : j=0 := by simp at hj;omega
  subst j
  simpa using And.intro h rd

def emitted61 {n} (e : Expr61 n) (b : Nat) (gs : List Gate) (out : Nat) : Prop :=
  gs.length=size61 e ∧ tick61 gs=neg61 e ∧ safe61 (2*n) b gs ∧ 2*n≤out ∧ out<b+gs.length ∧
  ∀ p : List Bool, p.length=b → (run61 gs p).getD out false =
    eval61 (fun i => p.getD (2*n+i.val) false) e

theorem terminal61 (gs : List Gate) (p : List Bool) (g : Gate) :
    (run61 (gs++[g]) p).getD (p.length+gs.length) false =
      g.op.eval (g.inputs.map (fun i=>(run61 gs p).getD i false)) := by
  rw [runAppend61,← runSize61]
  simp [run61,Circuit.wires,List.getD_eq_getElem?_getD]

theorem binary61 {n b} (ht : 3*n≤b) (a c : Expr61 n) (l r : List Gate) (u v : Nat)
    (hl : emitted61 a b l u) (hr : emitted61 c (b+l.length) r v)
    (op : GateOp) (ok : op=.and ∨ op=.or) :
    emitted61 (if op=.and then .both a c else .either a c) b
      ((l++r)++[⟨op,[u,v]⟩]) (b+(l++r).length) := by
  obtain ⟨szl,nl,sl,lowu,hiu,vl⟩ := hl
  obtain ⟨szr,nr,sr,lowv,hiv,vr⟩ := hr
  have sf : safe61 (2*n) b ((l++r)++[⟨op,[u,v]⟩]) := by
    apply safeAppend61 (safeAppend61 sl sr)
    apply safeOne61
    · rcases ok with rfl|rfl <;> simp [shape61]
    · intro w hw
      simp at hw
      rcases hw with rfl|rfl <;> simp only [List.length_append] <;> omega
  have semantics (p : List Bool) (plen : p.length=b) :
      (run61 ((l++r)++[⟨op,[u,v]⟩]) p).getD (b+(l++r).length) false =
      op.eval [eval61 (fun i=>p.getD (2*n+i.val) false) a,eval61 (fun i=>p.getD (2*n+i.val) false) c] := by
    rw [←plen,terminal61,runAppend61]
    have ll := runSize61 l p
    have hr' := vr (run61 l p) (by omega)
    have inputs : (fun i : Fin n=>(run61 l p).getD (2*n+i.val) false) =
        (fun i : Fin n=>p.getD (2*n+i.val) false) := by
      funext i
      apply runKeep61
      have := i.isLt
      omega
    simp only [List.map_cons,List.map_nil,runKeep61 r (run61 l p) u (by omega),vl p plen,hr',inputs]
  rcases ok with rfl | rfl
  all_goals
    refine ⟨?_,?_,sf,by omega,by simp,?_⟩
    · simp [size61,szl,szr,Nat.add_assoc]
    · simp [tick61,List.filter_append] at nl nr ⊢
      simp [neg61,nl,nr]
    · intro p plen
      simpa [eval61,GateOp.eval] using semantics p plen

theorem emit61 {n} (e : Expr61 n) (b : Nat) (ht : 3*n≤b) :
    ∃ gs out, emitted61 e b gs out := by
  induction e generalizing b with
  | var i =>
    refine ⟨[],2*n+i.val,rfl,rfl,?_,by omega,?_,?_⟩
    · intro j hj; simp at hj
    · have := i.isLt; simp; omega
    · intro p hp; rfl
  | both a c ha hc =>
    obtain ⟨l,u,hl⟩ := ha b ht
    obtain ⟨r,v,hr⟩ := hc (b+l.length) (by omega)
    exact ⟨_,_,binary61 ht a c l r u v hl hr .and (Or.inl rfl)⟩
  | either a c ha hc =>
    obtain ⟨l,u,hl⟩ := ha b ht
    obtain ⟨r,v,hr⟩ := hc (b+l.length) (by omega)
    exact ⟨_,_,binary61 ht a c l r u v hl hr .or (Or.inr rfl)⟩
  | inv a ih =>
    obtain ⟨l,u,sz,nc,safe,low,hi,val⟩ := ih b ht
    let g : Gate := ⟨.not,[u]⟩
    refine ⟨l++[g],b+l.length,by simp [size61,sz],?_,?_,by omega,by simp,?_⟩
    · simp [tick61] at nc ⊢
      simp [g,neg61,nc]
    · apply safeAppend61 safe
      apply safeOne61
      · simp [shape61,g]
      · simpa [g] using And.intro low hi
    · intro p hp
      rw [←hp,terminal61]
      change (!((run61 l p).getD u false)) = (!(eval61 _ a))
      rw [val p hp]

end PEqualNP.Outside.L_meta_25561_aux




namespace PEqualNP.Outside.L_meta_25561_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

theorem build61 {n : Nat} (mate : Equiv.Perm (Fin n)) (e : Expr61 n) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (2*n) C ∧
      (∀ u v : Fin n, C.eval (oneEach u v)=eval61 (fun i=>decide (i=u) || decide (mate i=v)) e) ∧
      2*n≤C.output ∧ C.output<2*n+C.size ∧ PEqualNP.NotBracket.notCount C=neg61 e ∧
      (∀ g∈C.gates,g.op=.not → ∃ w, g.inputs=[w]) ∧ C.size=n+size61 e ∧
      ∀ i : Fin n, (∃ g∈C.gates,g.op=.or ∧ g.inputs=[i.val,n+(mate i).val]) ∧
        (C.gates.map (fun g=>g.inputs.count i.val)).sum=1 ∧
        (C.gates.map (fun g=>g.inputs.count (n+i.val))).sum=1 := by
  obtain ⟨s,out,len,tick,safe,lo,hi,value⟩ := emit61 e (3*n) (by omega)
  let p := pairedGates61 mate
  let C : Circuit := ⟨p++s,out⟩
  have lp : p.length=n := pairSize61 mate
  have sz : C.size=n+s.length := by simp [C,Circuit.size,lp]
  have safeM (g : Gate) (h : g∈s) : shape61 g ∧ ∀w∈g.inputs, 2*n≤w := by
    obtain ⟨j,lt,rfl⟩ := List.mem_iff_getElem.mp h
    exact ⟨(safe j lt).1,fun w hw => ((safe j lt).2 w hw).1⟩
  have raw (w : Nat) (hw : w<2*n) : (s.map (fun g=>g.inputs.count w)).sum=0 := by
    apply List.sum_eq_zero_iff.mpr
    intro a ha
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
    exact List.count_eq_zero.mpr (by intro h;have := (safeM g hg).2 w h;omega)
  refine ⟨C,?_,?_,?_,lo,by simpa only [sz] using (show out<2*n+(n+s.length) by omega),?_,?_,by rw [sz,len],?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hp|hs
    · exact pairFan61 mate g hp
    · obtain ⟨⟨ops,fan,_⟩,_⟩ := safeM g hs
      exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ops,fan⟩
  · intro j hj w hw
    change j<(p++s).length at hj
    have hGate : gateAt C j=(p++s)[j] := by
      change (p++s).getD j _ = _
      rw [List.getD_eq_getElem _ _ hj]
    rw [hGate] at hw
    by_cases pre : j<p.length
    · rw [List.getElem_append_left pre] at hw
      apply pairReads61 mate j pre w
      change w∈(p.getD j _).inputs
      rwa [List.getD_eq_getElem _ _ pre]
    · have lt : j-p.length<s.length := by simp at hj;omega
      rw [List.getElem_append_right (by omega)] at hw
      have top := ((safe _ lt).2 w hw).2
      omega
  · intro u v
    let x := oneEach u v
    have xl : x.length=2*n := by simp [x,oneEach];omega
    have pl : (run61 p x).length=3*n := by rw [runSize61,lp,xl];omega
    change (run61 (p++s) x).getD out false=_
    rw [runAppend61,value (run61 p x) pl]
    congr 1
    funext i
    exact wiresPair61 mate u v i
  · have pn : tick61 p=0 := pairNot61 mate
    change tick61 (p++s)=_
    simpa only [tick61,List.filter_append,List.length_append,Nat.zero_add] using
      (show tick61 p+tick61 s=neg61 e by omega)
  · intro g hg hnot
    rcases List.mem_append.mp hg with hp|hs
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      contradiction
    · exact (safeM g hs).1.2.2 hnot
  · intro i
    have h := pairCounts61 mate i
    have il := i.isLt
    refine ⟨⟨_,List.mem_append_left _ (pairGateMem61 mate i),rfl,rfl⟩,?_,?_⟩
    · change ((p++s).map _).sum=1
      rw [List.map_append,List.sum_append,raw _ (by omega),Nat.add_zero]
      exact h.1
    · change ((p++s).map _).sum=1
      rw [List.map_append,List.sum_append,raw _ (by omega),Nat.add_zero]
      exact h.2

end PEqualNP.Outside.L_meta_25561_aux


namespace PEqualNP.Outside.L_meta_25561_aux
open PEqualNP.Represents
theorem columnDegree61 {n : Nat} (hn : 13≤n) (i : Fin n) :
    (Finset.univ.filter (fun u => G61 u i=true)).card=4 := by
  let f := mate61 hn
  have inv (j : Fin n) : f (f j)=j := refInvol61 hn j
  have swap (u v : Fin n) : G61 u v = G61 (f v) (f u) := by
    have h := crossSymm61 hn u (f v)
    change G61 u (f (f v)) = G61 (f v) (f u) at h
    simpa only [inv] using h
  rw [←degree61 hn (f i)]
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    simpa [swap a i] using ha
  · intro a _ b _ eq
    exact f.injective eq
  · intro b hb
    refine ⟨f b,?_,inv b⟩
    simpa [swap (f b) i,inv] using hb

theorem rowD61 {n : Nat} (hn : 13≤n) (u v : Fin n) (huv : u≠v) :
    6 ≤ (Finset.univ.filter (fun col => G61 u col ≠ G61 v col)).card :=
  sep61 (G61 u) (G61 v) (degree61 hn u) (degree61 hn v) (noFour61 hn u v · · huv)
theorem colD61 {n : Nat} (hn : 13≤n) (x y : Fin n) (hxy : x≠y) :
    6 ≤ (Finset.univ.filter (fun row => G61 row x ≠ G61 row y)).card := by
  apply sep61 _ _ (columnDegree61 hn x) (columnDegree61 hn y)
  intro u v ux uy vx vy
  by_contra huv
  exact hxy (noFour61 hn u v x y huv ux vx uy vy)
end PEqualNP.Outside.L_meta_25561_aux

theorem PEqualNP.Outside.L_meta_25561 :
∀ (n : ℕ), 13 ≤ n →
  let offsets : Finset ℕ := {0, 1, 4, 6}
  let G := fun (u v : Fin n) => decide ((v.val + n - u.val) % n ∈ offsets)
  let mate := fun (source : Fin n) => (n + 1 - source.val) % n
  let signals := fun (u v : Fin n) => Finset.univ.filter
    (fun lit : Fin n => lit = u ∨ mate lit = v.val)
  (∀ i j : Fin n, i ≠ j → 6 ≤ (Finset.univ.filter (fun col => G i col ≠ G j col)).card) ∧
  (∀ i j : Fin n, i ≠ j → 6 ≤ (Finset.univ.filter (fun row => G row i ≠ G row j)).card) ∧
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C ∧
    PEqualNP.Represents.Represents G C ∧
    2 * n ≤ C.output ∧ C.output < 2 * n + C.size ∧
    PEqualNP.NotBracket.notCount C = 1 ∧
    (∀ g ∈ C.gates, g.op = .not → ∃ w : ℕ, g.inputs = [w]) ∧
    C.size ≤ (if n % 2 = 1 then 6 * n else 6 * n - 2) ∧
    ∀ i : Fin n,
      (∃ g ∈ C.gates, g.op = .or ∧ g.inputs = [i.val, n + mate i]) ∧
      (C.gates.map (fun g => g.inputs.count i.val)).sum = 1 ∧
      (C.gates.map (fun g => g.inputs.count (n + i.val))).sum = 1) ∧
  ¬ ∃ accept : Finset (Fin n) → Prop,
    (∀ S T, S ⊆ T → accept S → accept T) ∧
    ∀ u v : Fin n, accept (signals u v) ↔ G u v = true := by
  classical
  intro n hn
  dsimp only
  refine ⟨PEqualNP.Outside.L_meta_25561_aux.rowD61 hn,PEqualNP.Outside.L_meta_25561_aux.colD61 hn,?_,PEqualNP.Outside.L_meta_25561_aux.noMon61 hn⟩
  let f := PEqualNP.Outside.L_meta_25561_aux.mate61 hn
  have inv (i : Fin n) : f (f i)=i := PEqualNP.Outside.L_meta_25561_aux.refInvol61 hn i
  obtain ⟨e,sz,neg,cert⟩ := PEqualNP.Outside.L_meta_25561_aux.suffix61 hn
  obtain ⟨C,fan,read,eval,lo,hi,one,unary,cs,raw⟩ := PEqualNP.Outside.L_meta_25561_aux.build61 f e
  refine ⟨C,fan,read,?_,lo,hi,one.trans neg,unary,cs.trans_le sz,raw⟩
  intro u v
  rw [eval]
  have h := cert u (f v)
  change _=PEqualNP.Outside.L_meta_25561_aux.G61 u (f (f v)) at h
  rw [inv] at h
  refine Eq.trans ?_ h
  congr 1
  funext i
  have iff : f i=v ↔ i=f v := ⟨fun eq => by simpa only [inv] using congrArg f eq,
    fun eq => by rw [eq,inv]⟩
  by_cases hu : i=u <;> by_cases hv : i=f v <;> simp [iff,hu,hv,inv]
