import PEqualNP.Defs
import Mathlib.Data.Nat.Fib.Basic

namespace PEqualNP.Outside.L_lib_1216

def modL (d : Nat) := Nat.fib (d-1) + Nat.fib (d+1)
def wt (d : Nat) := Nat.fib (2*d-1)^2 * Nat.fib d^2 * ((modL d-1)/2)

lemma periodThree (k : Nat) : Nat.fib (k+3) % 2 = Nat.fib k % 2 := by
  have h := @Nat.fib_add_two k
  have h' := @Nat.fib_add_two (k+1)
  change Nat.fib (k+3) = Nat.fib (k+1) + Nat.fib (k+2) at h'
  omega

lemma fibParity (k : Nat) : Nat.fib k % 2 = if k % 3 = 0 then 0 else 1 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases small : k < 3
    · interval_cases k <;> decide
    · have h := ih (k-3) (by omega)
      have hp := periodThree (k-3)
      rw [show k-3+3=k by omega] at hp
      have hm : (k-3)%3 = k%3 := by omega
      simpa [hp, hm] using h

lemma arith (d : Nat) (hd : 2 ≤ d) (h3 : d%3 ≠ 0) :
    let M := modL d
    let A := Nat.fib (2*d-1)
    let B := Nat.fib (2*d-2)
    let C := Nat.fib d
    let D := Nat.fib (d-1)
    let h := (M-1)/2
    Nat.Coprime (wt d % M) M ∧ (A : ZMod M) + B = 0 ∧
      (C : ZMod M) + 2*D = 0 ∧ (2 : ZMod M)*h = -1 := by
  dsimp only
  let M := modL d
  let A := Nat.fib (2*d-1)
  let B := Nat.fib (2*d-2)
  let C := Nat.fib d
  let D := Nat.fib (d-1)
  let H := (M-1)/2
  have hs : Nat.fib (d+1) = D + C := Nat.fib_add_one (by omega)
  have he : C+2*D=M := by dsimp [M,modL]; omega
  have hdouble : Nat.fib (2*d) = C*M := by
    rw [Nat.fib_two_mul, hs]; congr 1; omega
  have hab : A+B=C*M := by
    rw [← hdouble]; have h := @Nat.fib_add_two (2*d-2)
    rw [show 2*d-2+2=2*d by omega, show 2*d-2+1=2*d-1 by omega] at h
    simpa [A,B,Nat.add_comm] using h.symm
  have hcp : C%2=1 := by simp [C,fibParity,h3]
  have half : 2*H+1=M := by dsimp [H]; omega
  have ca : A.Coprime M := by
    apply Nat.Coprime.of_dvd_right (show M ∣ Nat.fib (2*d) from hdouble ▸ dvd_mul_left _ _)
    simpa [A,show 2*d-1+1=2*d by omega] using Nat.fib_coprime_fib_succ (2*d-1)
  have cd : C.Coprime D := by
    simpa [C,D,show d-1+1=d by omega] using (Nat.fib_coprime_fib_succ (d-1)).symm
  have c2 : C.Coprime 2 := Nat.coprime_two_right.mpr ⟨C/2, by omega⟩
  have cc : C.Coprime M := by rw [← he, Nat.coprime_self_add_right]; exact c2.mul_right cd
  have ch : H.Coprime M := by rw [← half, Nat.add_comm, Nat.coprime_add_mul_right_right]; simp
  have za : (A : ZMod M) + B = 0 := by
    rw [← Nat.cast_add,hab,Nat.cast_mul,ZMod.natCast_self,mul_zero]
  have zc : (C : ZMod M) + 2*D = 0 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self] using congrArg (fun z : Nat => (z : ZMod M)) he
  have zh : (2 : ZMod M)*H = -1 := by
    have hh := congrArg (fun z : Nat => (z : ZMod M)) half
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,ZMod.natCast_self] at hh
    exact eq_neg_of_add_eq_zero_left hh
  refine ⟨?_,za,zc,zh⟩
  change (A^2*C^2*H%M).gcd M = 1
  rw [← Nat.gcd_rec M (A^2*C^2*H), Nat.gcd_comm]
  exact ((ca.pow_left 2).mul_left (cc.pow_left 2)).mul_left ch

def Line {k : Nat} (z : Fin (k+1) → Bool) : Prop :=
  ∀ i : Fin k, z i.castSucc = false ∨ z i.succ = false

abbrev Col (k : Nat) (b : Bool) := {z : Fin (k+1) → Bool // z 0 = b ∧ Line z}

lemma line_cons {k : Nat} (a : Bool) (z : Fin (k+1) → Bool) :
    Line (Fin.cons a z) ↔ (a=false ∨ z 0=false) ∧ Line z := by
  rw [Line, Fin.forall_fin_succ]
  rfl

lemma colZero (b : Bool) : Nat.card (Col 0 b) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro x y; apply Subtype.ext; funext i; fin_cases i
    exact x.2.1.trans y.2.1.symm
  · exact ⟨⟨fun _ => b,rfl,fun i => i.elim0⟩⟩

abbrev Child (b : Bool) := {c : Bool // b=false ∨ c=false}

def splitCol (k : Nat) (b : Bool) : Col (k+1) b ≃ Σ c : Child b, Col k c.val where
  toFun x := by
    have E : Fin.cons b (fun j => x.val j.succ) = x.val := by
      funext i; refine Fin.cases x.2.1.symm (fun _ => rfl) i
    have ok := (line_cons b (fun j => x.val j.succ)).1 (E ▸ x.2.2)
    exact ⟨⟨_,ok.1⟩,⟨_,rfl,ok.2⟩⟩
  invFun x := ⟨Fin.cons b x.2.val,rfl,(line_cons ..).2 ⟨x.2.2.1.symm ▸ x.1.2,x.2.2.2⟩⟩
  left_inv x := by apply Subtype.ext; funext i; exact Fin.cases x.2.1.symm (fun _ => rfl) i
  right_inv := by
    rintro ⟨⟨c,hc⟩,⟨z,hz,hline⟩⟩
    change z 0 = c at hz
    subst c; rfl

lemma colStep (k : Nat) (b : Bool) : Nat.card (Col (k+1) b) =
    Nat.card (Col k false) + (if b then 0 else Nat.card (Col k true)) := by
  classical
  rw [Nat.card_congr (splitCol k b), Nat.card_sigma]
  have h := Finset.sum_subtype (Finset.univ.filter (fun c : Bool => b=false ∨ c=false))
    (p:=fun c => b=false ∨ c=false) (F:=inferInstance) (by simp) (fun c => Nat.card (Col k c))
  rw [← h,Finset.sum_filter,Fintype.sum_bool]
  cases b <;> simp [Nat.add_comm]

lemma colFib (k : Nat) (b : Bool) : Nat.card (Col k b) =
    if b then Nat.fib (k+1) else Nat.fib (k+2) := by
  induction k generalizing b with
  | zero => rw [colZero]; cases b <;> decide
  | succ k ih =>
    rw [colStep, ih, ih]
    cases b
    · change Nat.fib (k+2) + Nat.fib (k+1) = Nat.fib ((k+1)+2)
      rw [Nat.fib_add_two (n:=k+1),Nat.add_comm]
    · exact Nat.add_zero _

def tails (d : Nat) : Fin 6 → Nat := ![0,2*d-3,d-2,d-2,2*d-3,0]
abbrev V (t : Fin 6 → Nat) := Sigma (fun i : Fin 6 => Fin (t i + 1))
def rootV (t : Fin 6 → Nat) (i : Fin 6) : V t := ⟨i,0⟩
def near (a b : Nat) : Prop := a+1=b ∨ b+1=a
def Adj {t : Fin 6 → Nat} (p q : V t) : Prop :=
  (p.1=q.1 ∧ near p.2.val q.2.val) ∨ (p.2.val=0 ∧ q.2.val=0 ∧ near p.1.val q.1.val)

lemma extV {t : Fin 6 → Nat} {p q : V t} (h : p.1.val=q.1.val) (h' : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨i,a⟩; rcases q with ⟨j,b⟩
  have he : i=j := Fin.ext h
  subst j; congr 1; exact Fin.ext h'

lemma symAdj {t : Fin 6 → Nat} (p q : V t) : Adj p q ↔ Adj q p := by
  simp only [Adj,near]; tauto

lemma irreflAdj {t : Fin 6 → Nat} (p : V t) : ¬ Adj p p := by
  simp [Adj,near]

def color {t : Fin 6 → Nat} (p : V t) := decide ((p.1.val + p.2.val)%2=1)
lemma colors {t : Fin 6 → Nat} {p q : V t} (h : Adj p q) : color p ≠ color q := by
  simp only [color,ne_eq,decide_eq_decide] at *
  rcases h with ⟨he,h⟩ | ⟨h₁,h₂,h⟩
  · have := congrArg Fin.val he; rcases h with h | h <;> omega
  · rcases h with h | h <;> omega

noncomputable def nbr {t : Fin 6 → Nat} (p : V t) : Finset (V t) := by classical exact Finset.univ.filter (Adj p)
lemma mem_nbr {t : Fin 6 → Nat} {p q : V t} : q ∈ nbr p ↔ Adj p q := by classical simp [nbr]

lemma deg {t : Fin 6 → Nat} (p : V t) : (nbr p).card ≤ 3 := by
  classical
  let key (q : V t) := (q.1.val,q.2.val)
  have inj : Function.Injective key := fun a b h => extV (congrArg Prod.fst h) (congrArg Prod.snd h)
  rw [← Finset.card_image_of_injective (nbr p) inj]
  by_cases z : p.2.val=0
  · let Q : Finset (Nat × Nat) := {(p.1.val,1),(p.1.val-1,0),(p.1.val+1,0)}
    have sub : (nbr p).image key ⊆ Q := by
      intro v hv; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      have H := mem_nbr.mp hq
      simp only [Q,key,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
      rcases H with ⟨h,h'⟩ | ⟨_,h,h'⟩
      · have := congrArg Fin.val h; rcases h' with h' | h' <;> omega
      · rcases h' with h' | h' <;> omega
    apply (Finset.card_le_card sub).trans
    exact (Finset.card_insert_le ..).trans (by have := Finset.card_insert_le (p.1.val-1,0) ({(p.1.val+1,0)} : Finset (Nat×Nat)); simpa using Nat.add_le_add_right this 1)
  · let Q : Finset (Nat × Nat) := {(p.1.val,p.2.val+1),(p.1.val,p.2.val-1)}
    have sub : (nbr p).image key ⊆ Q := by
      intro v hv; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      have H := mem_nbr.mp hq
      simp only [Q,key,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
      rcases H with ⟨h,h'⟩ | ⟨h,_,_⟩
      · have := congrArg Fin.val h; rcases h' with h' | h' <;> omega
      · exact (z h).elim
    apply (Finset.card_le_card sub).trans
    exact (Finset.card_insert_le ..).trans (by simp)

lemma lastPorts (d : Nat) (k : Fin 6) (hk : k=0 ∨ k=5) :
    (nbr (rootV (tails d) k)).card=1 := by
  classical
  rcases hk with rfl | rfl
  · have h : nbr (rootV (tails d) 0) = {rootV (tails d) 1} := by
      ext q; rw [mem_nbr,Finset.mem_singleton]
      constructor
      · rintro (⟨he,hd⟩ | ⟨_,hz,hd⟩)
        · rcases q with ⟨i,j⟩; change (0 : Fin 6)=i at he; subst i
          have hj : j.val<1 := j.isLt
          change near 0 j.val at hd; unfold near at hd; omega
        · apply extV
          · change q.1.val = 1
            change near 0 q.1.val at hd; rcases hd with hd | hd <;> omega
          · exact hz
      · rintro rfl; exact Or.inr ⟨rfl,rfl,Or.inl rfl⟩
    simp [h]
  · have h : nbr (rootV (tails d) 5) = {rootV (tails d) 4} := by
      ext q; rw [mem_nbr,Finset.mem_singleton]
      constructor
      · rintro (⟨he,hd⟩ | ⟨_,hz,hd⟩)
        · rcases q with ⟨i,j⟩; change (5 : Fin 6)=i at he; subst i
          have hj : j.val<1 := j.isLt
          change near 0 j.val at hd; unfold near at hd; omega
        · have hh := q.1.isLt
          apply extV
          · change q.1.val = 4
            change near 5 q.1.val at hd; rcases hd with hd | hd <;> omega
          · exact hz
      · rintro rfl; exact Or.inr ⟨rfl,rfl,Or.inr rfl⟩
    simp [h]

lemma ncardV (d : Nat) (hd : 2≤d) : Fintype.card (V (tails d))=6*d-4 := by
  change Fintype.card (Sigma (fun i : Fin 6 => Fin (tails d i+1))) = _
  rw [Fintype.card_sigma]
  calc
    _ = ∑ i : Fin 6, (tails d i + 1) := Finset.sum_congr rfl fun i _ => Fintype.card_fin _
    _ = _ := by simp [Fin.sum_univ_succ,tails]; omega

def slot {t : Fin 6 → Nat} (cap : Nat) (p : V t) := p.1.val*cap+p.2.val

lemma bags (d : Nat) (hd : 2≤d) :
    ∃ (l : Nat) (bag : Fin l → Finset (V (tails d))),
      l ≤ 2*(6*d-4)+1 ∧
      (∀ k,rootV (tails d) 0 ∈ bag k ∧ rootV (tails d) 5 ∈ bag k ∧ (bag k).card ≤ 8) ∧
      (∀ v, ∃ k, v ∈ bag k) ∧ (∀ u v, Adj u v → ∃ k, u ∈ bag k ∧ v ∈ bag k) ∧
      ∀ v i j k, i≤j → j≤k → v∈bag i → v∈bag k → v∈bag j := by
  classical
  let t := tails d
  let cap := 2*d-2
  have pos : 0<cap := by dsimp [cap]; omega
  have depth (p : V t) : p.2.val < cap := by
    rcases p with ⟨i,z⟩; have h := z.isLt
    fin_cases i <;> simp [t,tails] at h <;> dsimp [cap] <;> omega
  have inj : Function.Injective (slot (t:=t) cap) := by
    intro a b h
    have divi (p : V t) : slot cap p / cap = p.1.val := by
      rw [slot,Nat.mul_comm, Nat.mul_add_div pos, Nat.div_eq_of_lt (depth p),Nat.add_zero]
    have remd (p : V t) : slot cap p % cap = p.2.val := by simp [slot,Nat.mod_eq_of_lt (depth p)]
    apply extV
    · rw [← divi a, h, divi]
    · rw [← remd a,h,remd]
  have below (p : V t) : slot cap p < 6*cap := by
    calc
      slot cap p < p.1.val*cap + cap := Nat.add_lt_add_left (depth p) _
      _ = (p.1.val+1)*cap := (Nat.succ_mul _ _).symm
      _ ≤ 6*cap := Nat.mul_le_mul_right _ p.1.isLt
  let rootset := Finset.univ.image (rootV t)
  let bucket (s : Nat) := Finset.univ.filter (fun v : V t => slot cap v=s)
  let bag (k : Fin (6*cap)) := rootset ∪ (bucket k.val ∪ bucket (k.val+1))
  have inRoot (v : V t) : v ∈ rootset ↔ v.2.val=0 := by
    constructor
    · intro h; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h; rfl
    · intro h; exact Finset.mem_image.mpr ⟨v.1,by simp,extV rfl h.symm⟩
  have mem (v : V t) (k : Fin (6*cap)) : v∈bag k ↔ v.2.val=0 ∨ slot cap v=k.val ∨ slot cap v=k.val+1 := by
    simp only [bag,bucket,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,inRoot]
  have one (s : Nat) : (bucket s).card ≤ 1 := by
    apply Finset.card_le_one.mpr; intro a ha b hb
    exact inj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  refine ⟨6*cap,bag,by dsimp [cap]; omega,?_,?_,?_,?_⟩
  · intro k; refine ⟨(mem ..).2 (.inl rfl),(mem ..).2 (.inl rfl),?_⟩
    have h₁ : rootset.card ≤ 6 := (Finset.card_image_le).trans (by simp)
    have h₂ := Finset.card_union_le rootset (bucket k.val ∪ bucket (k.val+1))
    have h₃ := Finset.card_union_le (bucket k.val) (bucket (k.val+1))
    have h₄ := one k.val; have h₅ := one (k.val+1); change (rootset ∪ _).card ≤ 8; omega
  · intro v; exact ⟨⟨_,below v⟩,(mem ..).2 (.inr (.inl rfl))⟩
  · intro u v h
    rcases h with ⟨he,h⟩ | ⟨hu,hv,_⟩
    · have h' : u.1.val*cap=v.1.val*cap := congrArg (fun i : Fin 6 => i.val*cap) he
      rcases h with h | h
      · exact ⟨⟨_,below u⟩,(mem ..).2 (.inr (.inl rfl)),(mem ..).2 (.inr (.inr (by dsimp [slot]; omega)))⟩
      · exact ⟨⟨_,below v⟩,(mem ..).2 (.inr (.inr (by dsimp [slot]; omega))),(mem ..).2 (.inr (.inl rfl))⟩
    · exact ⟨⟨_,below u⟩,(mem ..).2 (.inl hu),(mem ..).2 (.inl hv)⟩
  · intro v i j k hij hjk hi hk
    rw [mem] at hi hk ⊢; change i.val≤j.val at hij; change j.val≤k.val at hjk; omega

open scoped Classical

def PinOK (x y : Bool) (b : Fin 6 → Bool) : Prop := b 0=x ∧ b 5=y ∧ Line b
abbrev Pat (x y : Bool) := {b : Fin 6 → Bool // PinOK x y b}
abbrev Fiber (t : Fin 6 → Nat) (x y : Bool) := Sigma (fun b : Pat x y => ∀ i, Col (t i) (b.val i))

def Indep {t : Fin 6 → Nat} (z : V t → Bool) : Prop := ∀ p q, Adj p q → z p=false ∨ z q=false

lemma line_of_ind {t : Fin 6 → Nat} {z : V t → Bool} (h : Indep z) :
    Line (fun i => z (rootV t i)) ∧ ∀ i : Fin 6, Line (fun j => z ⟨i,j⟩) := by
  constructor
  · intro j; exact h _ _ (.inr ⟨rfl,rfl,.inl rfl⟩)
  · intro i j; exact h _ _ (.inl ⟨rfl,.inl rfl⟩)

lemma line_pair {k : Nat} {z : Fin (k+1) → Bool} (h : Line z) (u v : Fin (k+1))
    (huv : near u.val v.val) : z u=false ∨ z v=false := by
  have go (a b : Fin (k+1)) (e : a.val+1=b.val) : z a=false ∨ z b=false := by
    let j : Fin k := ⟨a.val,by have := b.isLt; omega⟩
    have he : j.succ=b := Fin.ext e
    have ha : j.castSucc=a := Fin.ext rfl
    simpa only [ha,he] using h j
  exact huv.elim (go u v) (fun hh => (go v u hh).symm)

lemma ind_of_line {t : Fin 6 → Nat} {z : V t → Bool} (hb : Line (fun i => z (rootV t i)))
    (hc : ∀ i : Fin 6, Line (fun j => z ⟨i,j⟩)) : Indep z := by
  rintro ⟨i,a⟩ ⟨j,b⟩ (⟨he,h⟩ | ⟨ha,hb',h⟩)
  · change i=j at he; subst j; exact line_pair (hc i) a b h
  · have e : a=0 := Fin.ext ha; have f : b=0 := Fin.ext hb'; subst a; subst b
    exact line_pair hb i j h

abbrev Label (t : Fin 6 → Nat) (x y : Bool) := {z : V t → Bool //
  Indep z ∧ z (rootV t 0)=x ∧ z (rootV t 5)=y}

def labelEquiv (t : Fin 6 → Nat) (x y : Bool) : Label t x y ≃ Fiber t x y where
  toFun z := ⟨⟨fun i => z.val (rootV t i),z.2.2.1,z.2.2.2,(line_of_ind z.2.1).1⟩,
    fun i => ⟨fun j => z.val ⟨i,j⟩,rfl,(line_of_ind z.2.1).2 i⟩⟩
  invFun v := by
    let z : V t → Bool := fun p => (v.2 p.1).val p.2
    have he : (fun i => z (rootV t i)) = v.1.val := funext (fun i => (v.2 i).2.1)
    exact ⟨z,ind_of_line (he ▸ v.1.2.2.2) (fun i => (v.2 i).2.2),
      ((v.2 0).2.1.trans v.1.2.1),((v.2 5).2.1.trans v.1.2.2.1)⟩
  left_inv := by intro z; rfl
  right_inv := by
    rintro ⟨⟨b,hb⟩,cc⟩
    have he : (fun i => (cc i).val 0)=b := funext (fun i => (cc i).2.1)
    apply Sigma.ext (Subtype.ext he)
    apply Function.hfunext (by rfl)
    intro i j hij; have hij' : i=j := eq_of_heq hij; subst j
    have aux {a c : Bool} (u : Col (t i) a) (v : Col (t i) c) (h : a=c) (hz : u.val=v.val) : HEq u v := by
      subst c; exact heq_of_eq (Subtype.ext hz)
    exact aux _ _ (cc i).2.1 rfl

noncomputable def subsetBits {t : Fin 6 → Nat} {N : Nat} (e : V t ≃ Fin N) : Finset (Fin N) ≃ (V t → Bool) := by
  classical
  exact {toFun := fun I p => decide (e p ∈ I)
         invFun := fun z => Finset.univ.filter (fun j => z (e.symm j)=true)
         left_inv := by intro I; ext j; simp
         right_inv := by intro z; funext p; simp}

noncomputable def portNB {t : Fin 6 → Nat} {N : Nat} (e : V t ≃ Fin N) (i : Fin N) := (nbr (e.symm i)).map e.toEmbedding

lemma portMem {t : Fin 6 → Nat} {N : Nat} (e : V t ≃ Fin N) (i j : Fin N) :
    j∈portNB e i ↔ Adj (e.symm i) (e.symm j) := by
  classical
  change j ∈ (nbr (e.symm i)).map e.toEmbedding ↔ _
  rw [← mem_nbr]; exact Finset.mem_map_equiv

def Phys {t : Fin 6 → Nat} {N : Nat} (e : V t ≃ Fin N) (x y : Bool) (I : Finset (Fin N)) : Prop :=
  (∀ u∈I, ∀ v∈portNB e u, v∉I) ∧ decide (e (rootV t 0)∈I)=x ∧ decide (e (rootV t 5)∈I)=y

lemma physical {t : Fin 6 → Nat} {N : Nat} (e : V t ≃ Fin N) (x y : Bool) (I : Finset (Fin N)) :
    Phys e x y I ↔ Indep (subsetBits e I) ∧ subsetBits e I (rootV t 0)=x ∧ subsetBits e I (rootV t 5)=y := by
  classical
  apply and_congr_left; intro _
  constructor
  · intro h p q ha
    by_cases hp : e p∈I
    · right; have hx := h _ hp (e q) ((portMem e ..).2 (by simpa using ha))
      simpa [subsetBits] using hx
    · left; simpa [subsetBits] using hp
  · intro h u hu v hv hv'
    have := h (e.symm u) (e.symm v) ((portMem e ..).1 hv)
    simpa [subsetBits,hu,hv'] using this

lemma counts {t : Fin 6 → Nat} {N : Nat} (e : V t ≃ Fin N) (x y : Bool) :
    Nat.card {I // Phys e x y I} = ∑ b : Pat x y, ∏ i : Fin 6,
      (if b.val i then Nat.fib (t i+1) else Nat.fib (t i+2)) := by
  classical
  rw [Nat.card_congr (((subsetBits e).subtypeEquiv (physical e x y)).trans (labelEquiv t x y))]
  change Nat.card (Sigma _) = _
  rw [Nat.card_sigma]; apply Finset.sum_congr rfl; intro b _; rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => colFib (t i) (b.val i)

def poly {R : Type} [CommSemiring R] (x y : Bool) (A B C D : R) : R :=
    A^2*(C^2+2*C*D) +
    (if x then 0 else A*B*C*(C+D)) + (if y then 0 else A*B*C*(C+D)) +
    (if x || y then 0 else B^2*C^2)

lemma poly_eval {R : Type} [CommRing R] (x y : Bool) (A B C D h : R)
    (h₁ : A+B=0) (h₂ : C+2*D=0) (h₃ : 2*h = -1) :
    poly x y A B C D = if x=y then 0 else A^2*C^2*h := by
  have b : B = -A := by linear_combination h₁
  have c : C = -2*D := by linear_combination h₂
  subst B; subst C
  cases x <;> cases y <;> simp [poly] <;>
    first | ring1 | linear_combination (-2*A^2*D^2)*h₃

open scoped Classical

def monom (A B C D : Nat) (b : Fin 6 → Bool) : Nat :=
  (if b 1 then B else A)*(if b 2 then D else C)*(if b 3 then D else C)*(if b 4 then B else A)

def patList (x y : Bool) : List (Fin 6 → Bool) :=
  [![x,false,false,false,false,y],![x,false,true,false,false,y],![x,false,false,true,false,y]] ++
  (if x then [] else [![x,true,false,false,false,y],![x,true,false,true,false,y]]) ++
  (if y then [] else [![x,false,false,false,true,y],![x,false,true,false,true,y]]) ++
  (if x || y then [] else [![x,true,false,false,true,y]])

lemma patOK : ∀ (x y : Bool) (b : Fin 6 → Bool), b ∈ patList x y ↔ PinOK x y b := by
  unfold PinOK Line
  decide +kernel

lemma patND : ∀ x y, (patList x y).Nodup := by decide +kernel

lemma backbone (x y : Bool) (A B C D : Nat) :
    ∑ b : Pat x y, monom A B C D b.val = poly x y A B C D := by
  classical
  rw [← Finset.sum_subtype (patList x y).toFinset (p:=PinOK x y) (F:=inferInstance)
    (fun b => List.mem_toFinset.trans (patOK x y b)) (monom A B C D), List.sum_toFinset _ (patND x y)]
  cases x <;> cases y <;> simp [patList,monom,poly] <;> ring

lemma residue {d N : Nat} (hd : 2≤d) (h3 : d%3≠0) (e : V (tails d) ≃ Fin N) (x y : Bool) :
    Nat.card {I // Phys e x y I} % modL d = if x=y then 0 else wt d % modL d := by
  let A := Nat.fib (2*d-1)
  let B := Nat.fib (2*d-2)
  let C := Nat.fib d
  let D := Nat.fib (d-1)
  have sumEq : Nat.card {I // Phys e x y I} = poly x y A B C D := by
    rw [counts,← backbone]; apply Finset.sum_congr rfl
    intro b hb
    simp only [Fin.prod_univ_succ,Finset.prod_empty,Finset.univ_eq_empty,Finset.prod_const_one]
    change (if b.val 0 then Nat.fib 1 else Nat.fib 2)*
      ((if b.val 1 then Nat.fib (2*d-3+1) else Nat.fib (2*d-3+2))*
      ((if b.val 2 then Nat.fib (d-2+1) else Nat.fib (d-2+2))*
      ((if b.val 3 then Nat.fib (d-2+1) else Nat.fib (d-2+2))*
      ((if b.val 4 then Nat.fib (2*d-3+1) else Nat.fib (2*d-3+2))*
      ((if b.val 5 then Nat.fib 1 else Nat.fib 2)*1))))) = _
    simp only [Nat.fib_one,Nat.fib_two,ite_self,one_mul,mul_one,show 2*d-3+1=2*d-2 by omega,
      show 2*d-3+2=2*d-1 by omega,show d-2+1=d-1 by omega,show d-2+2=d by omega,monom,A,B,C,D,mul_assoc]
  rw [sumEq]
  obtain ⟨_,ha,hc,hh⟩ := arith d hd h3
  have Z := poly_eval (R:=ZMod (modL d)) x y (A:ZMod _) (B:ZMod _) (C:ZMod _) (D:ZMod _)
    (((modL d-1)/2 : Nat) : ZMod _) ha hc hh
  have co : ((poly x y A B C D : Nat) : ZMod (modL d)) = poly x y (A:ZMod _) B C D := by
    cases x <;> cases y <;> simp [poly]
  by_cases eq : x=y
  · rw [if_pos eq] at Z ⊢
    have w := (ZMod.natCast_eq_natCast_iff' _ 0 _).1 (co.trans (Z.trans Nat.cast_zero.symm))
    simpa using w
  · rw [if_neg eq] at Z ⊢
    apply (ZMod.natCast_eq_natCast_iff' ..).1
    simpa only [wt,A,C,Nat.cast_mul,Nat.cast_pow] using co.trans Z

set_option maxHeartbeats 1500000 in
theorem realization : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ d : Nat, 2 ≤ d → d % 3 ≠ 0 →
  let M := Nat.fib (d-1) + Nat.fib (d+1)
  let c := (Nat.fib (2*d-1)^2 * Nat.fib d^2 * ((M-1)/2)) % M
  Nat.Coprime c M ∧
  ∃ (N : Nat) (nb : Fin N → Finset (Fin N)) (shore : Fin N → Bool)
    (left right : Fin N),
    N = 6*d-4 ∧ shore left = false ∧ shore right = true ∧
    (nb left).card = 1 ∧ (nb right).card = 1 ∧
    (∀ v, v ∉ nb v ∧ (nb v).card ≤ 3) ∧
    (∀ u v, v ∈ nb u ↔ u ∈ nb v) ∧ (∀ u, ∀ v ∈ nb u, shore u ≠ shore v) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
      l ≤ 2*N+1 ∧ (∀ t, left ∈ bag t ∧ right ∈ bag t ∧ (bag t).card ≤ 8) ∧
      (∀ v, ∃ t, v ∈ bag t) ∧ (∀ u v, v ∈ nb u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
    ∀ x y : Bool,
      ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ u ∈ I, ∀ v ∈ nb u, v ∉ I) ∧ decide (left ∈ I) = x ∧
        decide (right ∈ I) = y)).card % M = if x = y then 0 else c) := by
  classical
  intro d hd h3
  dsimp only
  refine ⟨(arith d hd h3).1,?_⟩
  let t := tails d
  let N := Fintype.card (V t)
  let e : V t ≃ Fin N := Fintype.equivFin _
  refine ⟨N,portNB e,fun i => color (e.symm i),e (rootV t 0),e (rootV t 5),ncardV d hd,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change color (e.symm (e (rootV t 0))) = false
    rw [e.symm_apply_apply]; rfl
  · change color (e.symm (e (rootV t 5))) = true
    rw [e.symm_apply_apply]; simp [color,rootV]
  · simpa only [portNB,Finset.card_map,e.symm_apply_apply] using lastPorts d 0 (.inl rfl)
  · simpa only [portNB,Finset.card_map,e.symm_apply_apply] using lastPorts d 5 (.inr rfl)
  · intro v; refine ⟨fun h => irreflAdj _ ((portMem e ..).1 h),?_⟩
    simpa only [portNB,Finset.card_map] using deg (e.symm v)
  · intro i j; rw [portMem,portMem]; apply symAdj
  · intro i j h; exact colors ((portMem e ..).1 h)
  · obtain ⟨l,bs,hl,hb,hv,he,hint⟩ := bags d hd
    refine ⟨l,fun k => (bs k).map e.toEmbedding,by simpa only [show N = 6*d-4 from ncardV d hd] using hl,?_,?_,?_,?_⟩
    · intro k; simpa only [Finset.mem_map_equiv,Equiv.symm_apply_apply,Finset.card_map] using hb k
    · intro v; obtain ⟨k,hk⟩ := hv (e.symm v); exact ⟨k,Finset.mem_map_equiv.2 hk⟩
    · intro u v h; obtain ⟨k,hu,hv'⟩ := he _ _ ((portMem e ..).1 h)
      exact ⟨k,Finset.mem_map_equiv.2 hu,Finset.mem_map_equiv.2 hv'⟩
    · intro v i j k hij hjk hi hk
      exact Finset.mem_map_equiv.2 (hint _ _ _ _ hij hjk (Finset.mem_map_equiv.1 hi) (Finset.mem_map_equiv.1 hk))
  · intro x y
    have H := residue hd h3 e x y
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at H
    let T := Finset.univ.filter (Phys e x y)
    calc
      _ = T.card % modL d := by
        apply congrArg (fun s : Finset (Finset (Fin N)) => s.card % modL d)
        ext I
        cases x <;> cases y <;> simp [T,Phys]
      _ = _ := by cases x <;> cases y <;> simpa [T,wt,modL] using H

end PEqualNP.Outside.L_lib_1216

theorem PEqualNP.Outside.L_lib_1216 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ d : Nat, 2 ≤ d → d % 3 ≠ 0 →
  let M := Nat.fib (d-1) + Nat.fib (d+1)
  let c := (Nat.fib (2*d-1)^2 * Nat.fib d^2 * ((M-1)/2)) % M
  Nat.Coprime c M ∧
  ∃ (N : Nat) (nb : Fin N → Finset (Fin N)) (shore : Fin N → Bool)
    (left right : Fin N),
    N = 6*d-4 ∧ shore left = false ∧ shore right = true ∧
    (nb left).card = 1 ∧ (nb right).card = 1 ∧
    (∀ v, v ∉ nb v ∧ (nb v).card ≤ 3) ∧
    (∀ u v, v ∈ nb u ↔ u ∈ nb v) ∧ (∀ u, ∀ v ∈ nb u, shore u ≠ shore v) ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
      l ≤ 2*N+1 ∧ (∀ t, left ∈ bag t ∧ right ∈ bag t ∧ (bag t).card ≤ 8) ∧
      (∀ v, ∃ t, v ∈ bag t) ∧ (∀ u v, v ∈ nb u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
    ∀ x y : Bool,
      ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ u ∈ I, ∀ v ∈ nb u, v ∉ I) ∧ decide (left ∈ I) = x ∧
        decide (right ∈ I) = y)).card % M = if x = y then 0 else c) := by
  exact PEqualNP.Outside.L_lib_1216.realization
