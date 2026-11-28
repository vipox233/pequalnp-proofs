import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1022


namespace CyclePins
open scoped Classical
abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n → F
abbrev P := Nat → Prop
def Good {n : Nat} (p : P) (v : F) (w : W n) : Prop :=
  (∀ i, p i.val → w i = 0) ∧ (∀ i, i.val = 0 → v*w i = 0) ∧
  (∀ i j, j.val = i.val+1 → w i*w j = 0)

def shift (p : P) : P := fun i => p (i+1)
abbrev Words (n : Nat) (p : P) (v : F) := {w : W n // Good p v w}
noncomputable def count (n : Nat) (p : P) (v : F) := Nat.card (Words n p v)

theorem good_succ {n} (p : P) (v : F) (w : W (n+1)) :
    Good p v w ↔ (p 0 → w 0 = 0) ∧ v*w 0 = 0 ∧ Good (shift p) (w 0) (Fin.tail w) := by
  constructor
  · rintro ⟨a,b,c⟩
    refine ⟨a 0,b 0 rfl,fun i hi => a i.succ hi,?_,?_⟩
    · intro i hi
      exact c 0 i.succ (by simp [hi])
    · intro i j hij
      exact c i.succ j.succ (by simp [hij])
  · rintro ⟨a,b,A,B,C⟩
    refine ⟨?_,?_,?_⟩
    · intro i
      refine Fin.cases a (fun k => ?_) i
      exact A k
    · intro i hi
      have e : i = 0 := Fin.ext hi
      simpa only [e] using b
    · intro i j
      refine Fin.cases (motive:=fun i => j.val=i.val+1 → w i*w j=0) ?_ (fun k => ?_) i
      · refine Fin.cases (motive:=fun j => j.val=(0 : Fin (n+1)).val+1 → w 0*w j=0) ?_ (fun l => ?_) j
        · simp
        · intro e
          exact B l (by simpa using e)
      · refine Fin.cases (motive:=fun j => j.val=k.succ.val+1 → w k.succ*w j=0) ?_ (fun l => ?_) j
        · simp
        · intro e
          exact C k l (by simpa using e)

def Head (p : P) (v b : F) : Prop := (p 0 → b=0) ∧ v*b=0

noncomputable def split {n : Nat} (p : P) (v : F) :
    Words (n+1) p v ≃ (Σ b : {b : F // Head p v b}, Words n (shift p) b.val) where
  toFun w :=
    let h := (good_succ p v w.val).mp w.property
    ⟨⟨w.val 0,h.1,h.2.1⟩,⟨Fin.tail w.val,h.2.2⟩⟩
  invFun z := ⟨Fin.cons z.1.val z.2.val, (good_succ _ _ _).mpr (by
    simpa only [Fin.cons_zero,Fin.tail_cons] using And.intro z.1.property.1 (And.intro z.1.property.2 z.2.property))⟩
  left_inv w := Subtype.ext (Fin.cons_self_tail _)
  right_inv := by
    rintro ⟨⟨b,hb⟩,⟨w,hw⟩⟩
    simp only [Fin.tail_cons]
    rfl

theorem card_split (n : Nat) (p : P) (v : F) :
    count (n+1) p v = ∑ b : F, if Head p v b then count n (shift p) b else 0 := by
  classical
  unfold count
  rw [Nat.card_congr (split p v), Nat.card_sigma]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (fun b : F => Nat.card (Words n (shift p) b))).symm

theorem pair_sum (f : F → Nat) : (∑ b : F, f b) = f 0 + f 1 := by
  have e : (Finset.univ : Finset F) = {0,1} := by decide
  rw [e,Finset.sum_pair (by decide : (0:F) ≠ 1)]

theorem count_fixed (n : Nat) (p : P) (v : F) (fix : p 0 ∨ v=1) :
    count (n+1) p v = count n (shift p) 0 := by
  classical
  rw [card_split,pair_sum]
  rcases fix with fix|rfl
  · simp [Head,fix]
  · simp [Head]

theorem count_free (n : Nat) (p : P) (hf : ¬ p 0) :
    count (n+1) p 0 = count n (shift p) 0 + count n (shift p) 1 := by
  classical
  rw [card_split,pair_sum]
  simp [Head,hf]

theorem empty_count (p : P) (v : F) : count 0 p v = 1 := by
  letI : Unique (Words 0 p v) := { default := ⟨fun i => i.elim0,
    fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩, uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩

def noPin : P := fun _ => False
theorem pathCount (n : Nat) : count n noPin 0 = Nat.fib (n+2) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [empty_count]; decide
  | one => rw [count_free 0 _ (by simp [noPin]),empty_count,empty_count]; decide
  | more n ih jh =>
    rw [count_free (n+1) _ (by simp [noPin])]
    change count (n+1) noPin 0 + count (n+1) noPin 1 = _
    rw [count_fixed _ _ _ (Or.inr rfl)]
    change count (n+1) noPin 0 + count n noPin 0 = _
    rw [ih,jh,@Nat.fib_add_two (n+2),Nat.add_comm]

def oddPin (k : Nat) : P := fun i => i % 2 = 1 ∧ i < 2*k
def evenPin (h : Nat) : P := fun i => i % 2 = 0 ∧ i < 2*h
theorem tail_pairs (k m : Nat) : count (2*k+m) (oddPin k) 0 = 2^k * Nat.fib (m+2) := by
  induction k with
  | zero =>
    have e : oddPin 0 = noPin := by funext i; simp [oddPin,noPin]
    simpa [e] using pathCount m
  | succ k ih =>
    have e : 2*(k+1)+m = ((2*k+m)+1)+1 := by omega
    rw [e, count_free _ _ (by simp [oddPin])]
    have pin : shift (oddPin (k+1)) 0 := by dsimp [shift,oddPin]; omega
    rw [count_fixed _ _ 0 (Or.inl pin),count_fixed _ _ 1 (Or.inl pin)]
    have d : shift (shift (oddPin (k+1))) = oddPin k := by
      funext i; apply propext; dsimp [shift,oddPin]; omega
    rw [d,ih,pow_succ]
    ring

theorem blockPaths (h m : Nat) (v : F) :
    count (2*h+m+1) (evenPin (h+1)) v = 2^h * Nat.fib (m+2) := by
  rw [count_fixed _ _ _ (Or.inl (by dsimp [evenPin]; omega))]
  have e : shift (evenPin (h+1)) = oddPin h := by
    funext i; apply propext; dsimp [shift,evenPin,oddPin]; omega
  rw [e,tail_pairs]
section Coordinates
theorem coordTools {n h : Nat} (e : Fin h ↪ Fin n) (D : Submodule F (W n))
    (desc : ∀ z : W n, z ∈ D ↔ ∀ i, (¬ ∃ k, i = e k) → z i = 0) :
    2 ^ Module.finrank F D = 2^h ∧ (∀ w : W n,
      (∀ z ∈ D, (∑ i, w i*z i)=0) ↔ ∀ k, w (e k) = 0) := by
  classical
  let ext (f : Fin h → F) (i : Fin n) : F := if H : ∃ k, i=e k then f H.choose else 0
  have ext_at (f : Fin h → F) (k : Fin h) : ext f (e k) = f k := by
    have H : ∃ l, e k = e l := ⟨k,rfl⟩
    simp only [ext,dif_pos H]
    rw [← e.injective H.choose_spec]
  have range (f : Fin h → F) : ext f ∈ D := (desc _).mpr (fun i hi => by simp [ext,hi])
  let E : D ≃ (Fin h → F) := {
    toFun := fun z k => z.val (e k)
    invFun := fun f => ⟨ext f,range f⟩
    left_inv := by
      intro z; apply Subtype.ext; funext i
      change ext (fun l => z.val (e l)) i = z.val i
      by_cases H : ∃ k, i=e k
      · obtain ⟨k,rfl⟩ := H; exact ext_at (fun l => z.val (e l)) k
      · rw [(desc _).mp z.property i H]; simp [ext,H]
    right_inv := fun f => funext (ext_at f) }
  constructor
  · have hc := Fintype.card_congr E
    rw [Module.card_eq_pow_finrank (K:=F) (V:=D), Fintype.card_fun,
      ZMod.card, Fintype.card_fin] at hc
    exact hc
  · intro w
    constructor
    · intro hw k
      have hm : Pi.single (e k) (1 : F) ∈ D := (desc _).mpr (by
        intro i hi; have ne : i ≠ e k := fun eq => hi ⟨k,eq⟩
        simp [Pi.single_apply,ne])
      have hz := hw _ hm
      simpa [Pi.single_apply,mul_ite] using hz
    · intro hw z hz
      apply Finset.sum_eq_zero
      intro i _
      by_cases H : ∃ k, i=e k
      · obtain ⟨k,rfl⟩ := H; rw [hw,zero_mul]
      · rw [(desc _).mp hz i H,mul_zero]
end Coordinates

section Rotation
variable {n : Nat} [NeZero n]

def natIx (i : Nat) : Fin n := ⟨i%n,Nat.mod_lt _ (NeZero.pos n)⟩

theorem ix_add (j : Fin n) (k : Nat) : natIx (j.val+k) = j + natIx k := by
  apply Fin.ext
  simp [natIx,Fin.val_add,Nat.add_mod]

theorem ix_succ (j : Fin n) : natIx (j.val+1) = j+1 := by
  rw [ix_add]; rfl

theorem cut (p : P) (hp : p 0) (hn : 1<n) (x : W n) :
    ((∀ i : Fin n, x i*x (i+1)=0) ∧ (∀ i : Fin n, p i.val → x i=0)) ↔ Good p 0 x := by
  have one : (1 : Fin n).val = 1 := by change 1%n=1; exact Nat.mod_eq_of_lt hn
  constructor
  · rintro ⟨H,F0⟩
    refine ⟨F0,by simp,?_⟩
    intro i j hj
    have ij : i+1=j := by
      apply Fin.ext
      rw [Fin.val_add,one,←hj,Nat.mod_eq_of_lt j.isLt]
    simpa only [ij] using H i
  · rintro ⟨F0,_,H⟩
    refine ⟨?_,F0⟩
    intro i
    by_cases hi : i.val+1<n
    · apply H; rw [Fin.val_add,one,Nat.mod_eq_of_lt hi]
    · have hi' : i.val+1=n := by have := i.isLt; omega
      have e : i+1=0 := by apply Fin.ext; rw [Fin.val_add,one,hi',Nat.mod_self]; rfl
      rw [e,F0 0 (by simpa using hp),mul_zero]
end Rotation

theorem canonical {n h : Nat} [NeZero n] (hn : 1<n) (hh : 1≤h) (hs : 2*h≤n)
    (j : Fin n) (D : Submodule F (W n))
    (desc : ∀ z : W n, z ∈ D ↔ ∀ i : Fin n, (¬ ∃ k : Fin h, i = natIx (j.val + 2*k.val)) → z i = 0) :
    2^Module.finrank F D * Nat.card {w : W n //
      (∀ i : Fin n, w i*w (natIx (i.val+1))=0) ∧ ∀ z ∈ D, (∑ i, w i*z i)=0} =
      2^(2*h-1)*Nat.fib (n-2*h+3) := by
  classical
  let t : Fin h ↪ Fin n := {
    toFun := fun k => ⟨2*k.val, by have := k.isLt; omega⟩
    inj' := by
      intro k l e
      have E := congrArg Fin.val e
      change 2*k.val=2*l.val at E
      apply Fin.ext; omega }
  let e := t.trans (Equiv.addLeft j).toEmbedding
  have he (k : Fin h) : e k = natIx (j.val+2*k.val) := by
    rw [ix_add]
    change j + t k = j + natIx (2*k.val)
    congr 1
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (t k).isLt).symm
  have supports (z : W n) : z ∈ D ↔ ∀ i, (¬ ∃ k : Fin h, i=e k) → z i=0 := by
    simpa only [he] using desc z
  obtain ⟨dim,orth⟩ := coordTools e D supports
  have chars (i : Fin n) : evenPin h i.val ↔ ∃ k, i=t k := by
    constructor
    · rintro ⟨par,small⟩
      refine ⟨⟨i.val/2,by omega⟩,Fin.ext ?_⟩
      change i.val=2*(i.val/2)
      omega
    · rintro ⟨k,rfl⟩
      change (2*k.val)%2=0 ∧ 2*k.val<2*h
      have := k.isLt
      omega
  let rot : W n ≃ W n := {
    toFun := fun w i => w (j+i)
    invFun := fun w i => w (-j+i)
    left_inv := fun w => funext fun i => by simp
    right_inv := fun w => funext fun i => by simp }
  have start : evenPin h 0 := by dsimp [evenPin]; omega
  have corr (w : W n) :
      ((∀ i : Fin n, w i*w (natIx (i.val+1))=0) ∧ ∀ z ∈ D, (∑ i, w i*z i)=0) ↔
        Good (evenPin h) 0 (rot w) := by
    rw [← cut _ start hn,orth]
    apply and_congr
    · simp_rw [ix_succ]
      constructor
      · intro a i; simpa [rot,add_assoc] using a (j+i)
      · intro a i; simpa [rot,add_assoc] using a (-j+i)
    · constructor
      · intro a i hi; obtain ⟨k,rfl⟩ := (chars i).mp hi; exact a k
      · intro a k; exact a (t k) ((chars _).mpr ⟨k,rfl⟩)
  rw [dim, Nat.card_congr (rot.subtypeEquiv corr)]
  change 2^h * count n (evenPin h) 0 = _
  have N : 2*(h-1)+(n-2*h+1)+1=n := by omega
  have H : h-1+1=h := by omega
  have pr := blockPaths (h-1) (n-2*h+1) 0
  rw [N,H] at pr
  rw [pr,← Nat.mul_assoc,← pow_add]
  have exp : h+(h-1)=2*h-1 := by omega
  rw [exp]


theorem positive : ∀ (a : ℕ) (ha : 0 < a) (h : ℕ), 3 ≤ a → 1 ≤ h → h ≤ a →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 2*a
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 1) ha)⟩ : Fin n)
  let even := fun (w : W) (i : Fin n) => if i.val % 2 = 0 then w i else 0
  let pin := fun (j : Fin n) (w : W) =>
    ∀ i : Fin n, (¬ ∃ k : Fin h, i = ix (j.val+2*k.val)) → w i = 0
  let best := 2^(2*h-1)*Nat.fib (n-2*h+3)
  ∀ D : Submodule F W, (∀ z ∈ D, even z ∈ D) → Module.finrank F D ≤ h →
    let hits := 2^(Module.finrank F D) * Nat.card {w : W //
      (∀ i, w i*w (ix (i.val+1)) = 0) ∧ (∀ z ∈ D, (∑ i, w i*z i) = 0)}
    let block := ∃ j : Fin n, ∀ z : W, z ∈ D ↔ pin j z
    block → hits = best := by
  intro a ha h ha3 hh hle
  letI : NeZero (2*a) := ⟨by omega⟩
  dsimp only
  intro D _ _ block
  obtain ⟨j,desc⟩ := block
  exact canonical (by omega) hh (by omega) j D desc


end CyclePins


namespace GapProducts

def f (s : Nat) := Nat.fib (s+2)
def mass (xs : List Nat) := (xs.map f).prod
def bad (xs : List Nat) := (xs.filter (fun x => x != 1)).length
def cap (xs : List Nat) := 2^(xs.length-1) * Nat.fib (xs.sum-xs.length+3)

theorem five (a : Nat) : Nat.fib (a+4) ≤ 5*Nat.fib (a+1) := by
  have i := @Nat.fib_add_two a
  have j := @Nat.fib_add_two (a+1)
  have k := @Nat.fib_add_two (a+2)
  have q := @Nat.fib_le_fib_succ a
  change Nat.fib (a+3)=Nat.fib (a+1)+Nat.fib (a+2) at j
  change Nat.fib (a+4)=Nat.fib (a+2)+Nat.fib (a+3) at k
  omega

theorem defect (a b : Nat) :
    Nat.fib (a+4)*Nat.fib (b+4) + Nat.fib (a+1)*Nat.fib (b+1) =
      2*Nat.fib (a+b+5) := by
  rw [show a+b+5 = (a+2)+(b+2)+1 by omega, Nat.fib_add (a+2) (b+2)]
  rw [@Nat.fib_add_two (a+2),@Nat.fib_add_two (b+2)]
  rw [@Nat.fib_add_two (a+1),@Nat.fib_add_two (b+1)]
  ring

theorem merge (p q : Nat) (hp : 0<p) :
    f p * f q ≤ 2*f (p+q-1) ∧
        (p≠1 → q≠1 → 26*(f p*f q) ≤ 25*(2*f (p+q-1))) := by
  rcases p with _|_ | a
  · omega
  · simp [f,Nat.add_comm 1, Nat.fib]
  rcases q with _|_ | b
  · have v := five a
    have d := @Nat.fib_add_two (a+2)
    have e := @Nat.fib_add_two (a+1)
    have two : Nat.fib 2 = 1 := rfl
    simp only [f,Nat.zero_add,Nat.add_zero,two,mul_one]
    change Nat.fib (a+4) ≤ 2*Nat.fib (a+3) ∧ (_ → _ → 26*Nat.fib (a+4) ≤ 25*(2*Nat.fib (a+3)))
    change Nat.fib (a+4)=Nat.fib (a+2)+Nat.fib (a+3) at d
    change Nat.fib (a+3)=Nat.fib (a+1)+Nat.fib (a+2) at e
    constructor <;> intros <;> omega
  · simp [f, Nat.fib, Nat.mul_comm]
  · have H := defect a b
    have J := Nat.mul_le_mul (five a) (five b)
    have e : a+2+(b+2)-1+2=a+b+5 := by omega
    simp only [f,e]
    constructor <;> intros <;> nlinarith only [H,J]

theorem perm {xs ys : List Nat} (p : xs.Perm ys) :
    mass xs = mass ys ∧ cap xs = cap ys ∧ bad xs = bad ys :=
  ⟨(p.map f).prod_eq,by simp only [cap,p.length_eq,p.sum_eq],
    (p.filter _).length_eq⟩

theorem cap_merge (p q : Nat) (zs : List Nat) (hp : 0<p) (hs : (p::q::zs).length ≤ (p::q::zs).sum) :
    cap (p::q::zs) = 2*cap ((p+q-1)::zs) := by
  simp only [cap,List.length_cons,List.sum_cons]
  simp only [List.length_cons,List.sum_cons] at hs
  have E : p+(q+zs.sum)-(zs.length+1+1)=(p+q-1)+zs.sum-(zs.length+1) := by omega
  rw [E]
  simp [pow_succ,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]

theorem bound (xs : List Nat) (hpos : 0<xs.length) (hs : xs.length ≤ xs.sum) :
    mass xs ≤ cap xs ∧ (2 ≤ bad xs → 26*mass xs ≤ 25*cap xs) := by
  have pp : ∃ p ∈ xs, 0<p := by
    by_contra! h
    have z : xs.sum=0 := List.sum_eq_zero_iff.mpr fun i hi => by have := h i hi; omega
    omega
  obtain ⟨p,hp,positive⟩ := pp
  have P := List.perm_cons_erase hp
  let ys := xs.erase p
  change xs.Perm (p::ys) at P
  obtain ⟨m,c,b⟩ := perm P
  rw [m,c,b]
  have hs' := P.sum_eq
  have hl' := P.length_eq
  cases he : ys with
  | nil =>
    simp only [he,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hs' hl'
    simp [mass,cap,bad,f,he,positive,show p-1+3=p+2 by omega]
    exact List.length_filter_le ..
  | cons q zs =>
    simp only [he] at *
    have S : (p::q::zs).length ≤ (p::q::zs).sum := by omega
    have st : ((p+q-1)::zs).length ≤ ((p+q-1)::zs).sum := by
      simp only [List.length_cons,List.sum_cons] at S ⊢; omega
    have smaller : ((p+q-1)::zs).length < xs.length := by simp_all
    have h := bound ((p+q-1)::zs) (by simp) st
    obtain ⟨u,v⟩ := merge p q positive
    have M : mass (p::q::zs) = (f p*f q)*mass zs := by simp [mass,Nat.mul_assoc]
    have N : mass ((p+q-1)::zs) = f (p+q-1)*mass zs := by simp [mass]
    rw [cap_merge p q zs positive S,M]
    rw [N] at h
    have u' := Nat.mul_le_mul_right (mass zs) u
    have ho := h.1
    constructor
    · nlinarith only [u',ho]
    · intro hz
      by_cases h1 : p=1 ∨ q=1
      · have bz : 2 ≤ bad ((p+q-1)::zs) := by
          rcases h1 with rfl|rfl
          · simpa [bad,Nat.add_comm 1] using hz
          · by_cases e : p=1 <;> simp [bad,List.filter_cons,e] at hz ⊢ <;> omega
        have hl := h.2 bz
        nlinarith only [hl,u']
      · push_neg at h1
        have loss := Nat.mul_le_mul_right (mass zs) (v h1.1 h1.2)
        nlinarith only [loss,ho]
termination_by xs.length

end GapProducts

namespace LocalLoss
open scoped Classical
abbrev F := ZMod 2
variable {I : Type} [Fintype I] [DecidableEq I]
def OK (G : SimpleGraph I) (T : Finset I) (w : I → F) : Prop :=
  (∀ i ∈ T, w i=0) ∧ ∀ i j, G.Adj i j → w i*w j=0

theorem editLoss (G : SimpleGraph I) (T M : Finset I) (s k : I)
    (L : (I → F) →ₗ[F] F) (hs : s ∈ M) (hk : k ∈ M) (sep : s≠k)
    (sfree : s ∉ T) (kfree : k ∉ T) (small : M.card≤5)
    (safe : ∀ i, i=s ∨ i=k → ∀ j, G.Adj i j → j∈T ∨ (j∈M ∧ j≠s ∧ j≠k))
    (coef : L (Pi.single k 1) ≠ 0) :
    32 * Nat.card {w : I → F // OK G T w ∧ w s * L w = 0} ≤
      31 * Nat.card {w : I → F // OK G T w} := by
  classical
  let u : I → F := Pi.single k 1
  let clear (w : I → F) : I → F := fun i => if i=s then 1 else if i∈M then 0 else w i
  let edit (w : I → F) : I → F := clear w + ((1-L (clear w))/L u) • u
  have away (w : I → F) {i : I} (hi : i∉M) : edit w i = w i := by
    have e : i≠s := fun h => hi (h ▸ hs)
    have f : i≠k := fun h => hi (h ▸ hk)
    simp [edit,clear,u,Pi.single_apply,hi,e,f]
  have atS (w : I → F) : edit w s = 1 := by simp [edit,clear,u,Pi.single_apply,sep]
  have vanish (w : I → F) {i : I} (hi : i∈M) (a : i≠s) (b : i≠k) :
      edit w i=0 := by simp [edit,clear,u,Pi.single_apply,a,b,hi]
  have value (w : I → F) : L (edit w) = 1 := by
    have hu : L u≠0 := coef
    simp only [edit,map_add,map_smul,smul_eq_mul]
    field_simp
    ring
  have ok (w : I → F) (hw : OK G T w) : OK G T (edit w) := by
    have pinned (i : I) (hi : i∈T) : edit w i=0 := by
      by_cases m : i∈M
      · exact vanish w m (fun e => sfree (e ▸ hi)) (fun e => kfree (e ▸ hi))
      · rw [away w m]; exact hw.1 i hi
    have neighbor (i : I) (active : i=s ∨ i=k) (j : I) (adj : G.Adj i j) :
        edit w j=0 := by
      rcases safe i active j adj with pin|⟨m,a,b⟩
      · exact pinned _ pin
      · exact vanish _ m a b
    refine ⟨pinned,?_⟩
    intro i j E
    by_cases ai : i=s ∨ i=k
    · rw [neighbor i ai j E,mul_zero]
    by_cases aj : j=s ∨ j=k
    · rw [neighbor j aj i E.symm,zero_mul]
    by_cases mi : i∈M
    · rw [vanish _ mi (fun e => ai (Or.inl e)) (fun e => ai (Or.inr e)),zero_mul]
    by_cases mj : j∈M
    · rw [vanish _ mj (fun e => aj (Or.inl e)) (fun e => aj (Or.inr e)),mul_zero]
    rw [away _ mi,away _ mj]
    exact hw.2 i j E
  let A := {w : I → F // OK G T w}
  let B := {w : A // w.val s * L w.val ≠ 0}
  let pack (w : A) : B × (M → F) :=
    (⟨⟨edit w.val,ok _ w.property⟩,by simp only [atS,value,mul_one]; exact one_ne_zero⟩,
     fun i => w.val i.val)
  have inject : Function.Injective pack := by
    intro w z hz
    apply Subtype.ext
    funext i
    by_cases m : i∈M
    · exact congrArg (fun v : B × (M→F) => v.2 ⟨i,m⟩) hz
    · have h := congrArg (fun v : B × (M→F) => v.1.val.val i) hz
      change edit w.val i=edit z.val i at h
      simpa only [away _ m] using h
  have bound := Fintype.card_le_of_injective pack inject
  rw [Fintype.card_prod,Fintype.card_fun,ZMod.card,Fintype.card_coe] at bound
  have cp : 2^M.card ≤ 32 := Nat.pow_le_pow_right (by decide : 0<2) small
  have cap := le_trans bound (Nat.mul_le_mul_left _ cp)
  let accept (w : A) := w.val s * L w.val=0
  let E : {w : I → F // OK G T w ∧ w s*L w=0} ≃ {w : A // accept w} :=
    ⟨fun w => ⟨⟨w.val,w.property.1⟩,w.property.2⟩,fun w => ⟨w.val.val,w.val.property,w.property⟩,
      fun _ => rfl,fun _ => rfl⟩
  have total := Fintype.card_subtype_compl accept
  change Fintype.card B = Fintype.card A - Fintype.card {w : A // accept w} at total
  have leA := Fintype.card_le_of_injective (fun w : {w : A // accept w} => w.val) Subtype.val_injective
  rw [Nat.card_congr E,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  change 32*Fintype.card {w : A // accept w} ≤ 31*Fintype.card A
  omega
end LocalLoss


namespace PinBasis
open scoped Classical
abbrev F := ZMod 2
variable {I : Type} [Fintype I] [DecidableEq I]
def Separates (D : Submodule F (I → F)) (T : Finset I) : Prop :=
  ∀ z ∈ D, (∀ i ∈ T, z i=0) → z=0

theorem pivots (D : Submodule F (I → F)) : ∃ T : Finset I, ∃ b : T → D,
    Separates D T ∧ T.card = Module.finrank F D ∧
      ∀ t i : T, (b t).val i.val = if i=t then 1 else 0 := by
  classical
  let S := Finset.univ.filter (Separates D)
  have top : Separates D Finset.univ := by intro z _ h; funext i; exact h i (Finset.mem_univ _)
  have mem (T : Finset I) : T∈S ↔ Separates D T := by simp [S]
  obtain ⟨T,m,minimal⟩ := S.exists_min_image Finset.card ⟨_,(mem _).mpr top⟩
  have sep := (mem _).mp m
  have witness (t : T) : ∃ z : D, ∀ i : T, z.val i.val = if i=t then 1 else 0 := by
    have ns : ¬ Separates D (T.erase t.val) := by
      intro H
      exact (Nat.not_le_of_gt (Finset.card_erase_lt_of_mem t.property)) (minimal _ ((mem _).mpr H))
    unfold Separates at ns
    push Not at ns
    obtain ⟨z,hz,all,nonzero⟩ := ns
    have bit : z t.val ≠ 0 := by
      intro zero; apply nonzero
      apply sep _ hz; intro i hi
      by_cases e : i=t.val
      · simpa [e] using zero
      · exact all i (Finset.mem_erase.mpr ⟨e,hi⟩)
    have one : z t.val=1 := by
      have binary : ∀ x : F, x=0 ∨ x=1 := by decide
      exact (binary _).resolve_left bit
    refine ⟨⟨z,hz⟩,?_⟩
    intro i; by_cases E : i=t
    · subst i; simpa using one
    · have ne : i.val ≠ t.val := fun u => E (Subtype.ext u)
      simpa [E] using all i.val (Finset.mem_erase.mpr ⟨ne,i.property⟩)
  choose b rows using witness
  let ev : D →ₗ[F] (T → F) := {
    toFun := fun z i => z.val i.val
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have inj : Function.Injective ev := by
    intro x y h
    have H : x.val-y.val=0 := sep _ (D.sub_mem x.property y.property) (by
      intro i hi; exact sub_eq_zero.mpr (congrFun h ⟨i,hi⟩))
    exact Subtype.ext (sub_eq_zero.mp H)
  have sur : Function.Surjective ev := by
    intro f
    refine ⟨∑ t : T, f t • b t,?_⟩
    funext i
    rw [map_sum,Finset.sum_apply]
    simp only [map_smul,Pi.smul_apply,smul_eq_mul]
    change (∑ t : T, f t * (b t).val i.val) = f i
    simp [rows,mul_ite]
  have equal := (LinearEquiv.ofBijective ev ⟨inj,sur⟩).finrank_eq
  refine ⟨T,b,sep,?_,rows⟩
  simpa using equal.symm

def erase (T : Finset I) (w : I → F) : I → F := fun i => if i ∈ T then 0 else w i
def dot (w z : I → F) : F := ∑ i, w i*z i
theorem recover {T : Finset I} {D : Submodule F (I → F)} (b : T → D)
    (rows : ∀ t i : T, (b t).val i.val = if i=t then 1 else 0)
    (w : I → F) (hw : ∀ z ∈ D, dot w z=0) (t : T) :
    w t.val = -dot (erase T w) (b t).val := by
  classical
  have separate : dot w (b t).val = w t.val + dot (erase T w) (b t).val := by
    unfold dot
    have orig : w t.val = ∑ i : I, if i=t.val then w i else 0 := by simp
    rw [orig,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i∈T
    · have key := rows t ⟨i,hi⟩
      by_cases e : i=t.val
      · subst i; simp [erase,t.property] at key ⊢; rw [key,mul_one]
      · have ne : (⟨i,hi⟩ : T) ≠ t := fun h => e (congrArg Subtype.val h)
        simp [ne] at key; simp [key,erase,hi,e]
    · have e : i ≠ t.val := fun h => hi (h ▸ t.property)
      simp [erase,hi,e]
  have h := hw _ (b t).property
  rw [separate] at h
  exact eq_neg_of_add_eq_zero_left h

end PinBasis

namespace CyclePins
open scoped Classical
open GapProducts (mass bad cap)

noncomputable def mask (n : Nat) (p : P) := List.ofFn fun i : Fin n => decide (p i.val)
def mesh (xs : List Nat) : List Bool := xs.flatMap fun a => true :: List.replicate a false

theorem mask_succ (m : Nat) (p : P) : mask (m+1) p = decide (p 0) :: mask m (shift p) := by
  rw [mask,List.ofFn_succ]
  rfl

theorem paths_form (m : Nat) (p : P) : ∃ a xs,
    mask m p = List.replicate a false ++ mesh xs ∧
    count m p 0 = GapProducts.f a * mass xs ∧
    count m p 1 = Nat.fib (a+1) * mass xs := by
  induction m generalizing p with
  | zero =>
    refine ⟨0,[],by simp [mask,mesh],?_,?_⟩ <;> rw [empty_count] <;> decide +revert
  | succ m ih =>
    obtain ⟨a,xs,H,A,B⟩ := ih (shift p)
    by_cases h : p 0
    · refine ⟨0,a::xs,?_,?_,?_⟩
      · simp [mask_succ,mesh,h,H]
      · rw [count_fixed _ _ _ (Or.inl h),A]
        simp [mass,GapProducts.f,Nat.fib]
      · rw [count_fixed _ _ _ (Or.inl h),A]
        simp [mass,GapProducts.f,Nat.fib]
    · refine ⟨a+1,xs,?_,?_,?_⟩
      · simp [mask_succ,List.replicate_succ,h,H]
      · rw [count_free _ _ h,A,B]
        unfold GapProducts.f
        rw [@Nat.fib_add_two (a+1)]
        ring
      · rw [count_fixed _ _ _ (Or.inr rfl),A]; rfl

theorem mesh_len (xs : List Nat) : (mesh xs).length=xs.length+xs.sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change ((true::List.replicate a false)++mesh xs).length = _
    simp [ih]; omega

theorem mesh_ones (xs : List Nat) : (mesh xs).count true=xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change ((true::List.replicate a false)++mesh xs).count true=_
    simp [ih,List.count_replicate]

theorem start_form (n : Nat) (p : P) (hn : 0<n) (start : p 0) : ∃ xs,
    mask n p=mesh xs ∧ count n p 0=mass xs := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨a,xs,H,A,_⟩ := paths_form m (shift p)
  refine ⟨a::xs,?_,?_⟩
  · simp [mask_succ,start,H,mesh]
  · rw [count_fixed _ _ _ (Or.inl start),A]; rfl

theorem split_one (xs : List Nat) (nonempty : xs ≠ []) (single : bad xs < 2) :
    ∃ u v a : Nat, xs = List.replicate u 1 ++ [a] ++ List.replicate v 1 := by
  induction xs with
  | nil => contradiction
  | cons q xs ih =>
    by_cases eq : q=1
    · subst q
      cases xs with
      | nil => exact ⟨0,0,1,rfl⟩
      | cons y ys =>
        obtain ⟨u,v,a,h⟩ := ih (by simp) (by simpa [bad] using single)
        exact ⟨u+1,v,a,by simp [List.replicate_succ,h]⟩
    · have none : (xs.filter (fun n => n != 1)).length=0 := by
        have hb : bad (q::xs) = (xs.filter (fun n => n != 1)).length+1 := by
          simp [bad,List.filter_cons,eq]
        rw [hb] at single; omega
      have all : ∀ x∈xs, x=1 := by
        intro x hx; by_contra h
        have hm : x ∈ xs.filter (fun n => n != 1) := List.mem_filter.mpr ⟨hx,by simp [h]⟩
        simp [List.length_eq_zero_iff.mp none] at hm
      refine ⟨0,xs.length,q,?_⟩
      simp only [List.replicate_zero,List.nil_append,List.singleton_append,List.cons.injEq,true_and]
      exact List.eq_replicate_of_mem all

theorem mesh_append (xs ys : List Nat) : mesh (xs++ys) = mesh xs ++ mesh ys := by simp [mesh]

theorem rotate_flat {xs : List Nat} (ne : xs≠[]) (flat : bad xs<2) :
    ∃ t k a : Nat, k+1=xs.length ∧ (mesh xs).rotate t = mesh (List.replicate k 1 ++ [a]) := by
  obtain ⟨u,v,a,rfl⟩ := split_one xs ne flat
  refine ⟨(mesh (List.replicate u 1 ++ [a])).length,v+u,a,by simp; omega,?_⟩
  rw [mesh_append, List.rotate_append_length_eq,←mesh_append]
  congr 1
  rw [List.replicate_add v u]
  simp only [List.append_assoc]

theorem stride (k a i : Nat) (hi : i < (mesh (List.replicate k 1 ++ [a])).length) :
    (mesh (List.replicate k 1 ++ [a]))[i] = true ↔ evenPin (k+1) i := by
  induction k generalizing i with
  | zero =>
    simp only [List.replicate_zero,List.nil_append] at hi ⊢
    change (true :: List.replicate a false ++ [])[i] = true ↔ _
    cases i with
    | zero => simp [evenPin]
    | succ i =>
      simp [evenPin,List.getElem_replicate]
      omega
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append] at hi ⊢
    change i < (true :: false :: mesh (List.replicate k 1 ++ [a])).length at hi
    change (true :: false :: mesh (List.replicate k 1 ++ [a]))[i] = true ↔ _
    cases i with
    | zero => simp [evenPin]
    | succ i =>
      cases i with
      | zero => simp [evenPin]
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [ih i (by simp at hi; omega)]
        unfold evenPin; omega
end CyclePins

namespace CyclePins
open scoped Classical
variable {n : Nat} [NeZero n]

def graph (n : Nat) [NeZero n] : SimpleGraph (Fin n) where
  Adj i j := i≠j ∧ (j=i+1 ∨ i=j+1)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem grCycle (hn : 1<n) (x : W n) :
    (∀ i j, (graph n).Adj i j → x i*x j=0) ↔ ∀ i : Fin n, x i*x (i+1)=0 := by
  have nz : (1 : Fin n)≠0 := by
    intro e
    have h := congrArg Fin.val e
    change 1%n=0 at h
    rw [Nat.mod_eq_of_lt hn] at h; omega
  constructor
  · intro H i
    apply H
    refine ⟨?_,Or.inl rfl⟩
    intro e; exact nz ((add_eq_left.mp e.symm))
  · intro H i j h
    rcases h.2 with rfl|rfl
    · exact H i
    · rw [mul_comm]; exact H j

theorem ix_val (i : Fin n) : natIx i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
theorem chart (hn : 1<n) (T : Finset (Fin n)) (j : Fin n) (hj : j∈T) (hsmall : 2*T.card≤n) :
    ∃ xs : List Nat, xs.length=T.card ∧ xs.length+xs.sum=n ∧
      Nat.card {w : W n // LocalLoss.OK (graph n) T w} = GapProducts.mass xs ∧
      (GapProducts.bad xs<2 → ∃ u : Fin n, ∀ t : Fin n, t∈T ↔
          ∃ k : Fin T.card, t=natIx (u.val+2*k.val)) := by
  classical
  let q : P := fun t => j + natIx t ∈ T
  have z : natIx (n:=n) 0=0 := by apply Fin.ext; simp [natIx]
  have start : q 0 := by simpa [q,z] using hj
  let rot : W n ≃ W n := {
    toFun := fun w i => w (j+i)
    invFun := fun w i => w (-j+i)
    left_inv := fun w => funext fun i => by simp
    right_inv := fun w => funext fun i => by simp }
  have corr (w : W n) : LocalLoss.OK (graph n) T w ↔ Good q 0 (rot w) := by
    rw [←cut q start hn]
    unfold LocalLoss.OK
    rw [grCycle hn]
    constructor
    · rintro ⟨p,c⟩
      exact ⟨fun i => by simpa [rot,add_assoc] using c (j+i),
        fun i hi => p (j+i) (by simpa [q,ix_val] using hi)⟩
    · rintro ⟨c,p⟩
      constructor
      · intro i hi; simpa [rot] using p (-j+i) (by simpa [q,ix_val] using hi)
      · intro i; simpa [rot,add_assoc] using c (-j+i)
  obtain ⟨xs,H,A⟩ := start_form n q (by omega) start
  have card : xs.length=T.card := by
    rw [←mesh_ones,←H,mask,List.count_ofFn]
    apply Finset.card_bij (fun i _ => j+i)
    · intro i hi; simpa [q,ix_val] using hi
    · intro i _ k _ h; exact add_left_cancel h
    · intro i hi; refine ⟨-j+i,?_,by simp⟩; simpa [q,ix_val] using hi
  have sz : xs.length+xs.sum=n := by rw [←mesh_len,←H]; simp [mask]
  refine ⟨xs,card,sz,(Nat.card_congr (rot.subtypeEquiv corr)).trans A,?_⟩
  intro flat
  have nonempty : xs≠[] := by intro e; simp [e] at sz; omega
  obtain ⟨t,k,a,hk,shape⟩ := rotate_flat nonempty flat
  let u : Fin n := j + natIx t
  have shown (i : Fin n) : u+i∈T ↔ evenPin T.card i.val := by
    have R : (mask n q).rotate t = mesh (List.replicate k 1 ++ [a]) := by simpa [H] using shape
    have hlen : (mesh (List.replicate k 1 ++ [a])).length=n := by rw [←R]; simp [mask]
    have hi : i.val < (mesh (List.replicate k 1 ++ [a])).length := by simpa [hlen] using i.isLt
    have equal := congrArg (fun l : List Bool => l[i.val]?) R
    change ((mask n q).rotate t)[i.val]? = _ at equal
    rw [List.getElem?_rotate (by simp [mask]),List.getElem?_eq_getElem hi] at equal
    have modlt : (i.val+t)%n < n := Nat.mod_lt _ (NeZero.pos n)
    simp only [mask,List.length_ofFn,List.getElem?_ofFn,modlt,dif_pos,Option.some.injEq] at equal
    have reindex : (natIx ((i.val+t)%n) : Fin n) = i+natIx t := by
      rw [←ix_add]; apply Fin.ext; simp [natIx]
    have b := stride k a i.val hi
    rw [←equal] at b
    simp only [decide_eq_true_eq] at b
    change (j + natIx ((i.val+t)%n) ∈ T ↔ evenPin (k+1) i.val) at b
    simp only [reindex,hk,card] at b
    simpa only [u,add_assoc,add_comm (natIx t) i] using b
  have pins (i : Fin n) : evenPin T.card i.val ↔ ∃ k : Fin T.card, i=natIx (2*k.val) := by
    constructor
    · rintro ⟨par,small⟩; refine ⟨⟨i.val/2,by omega⟩,Fin.ext ?_⟩
      change i.val=(2*(i.val/2))%n
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rintro ⟨k,rfl⟩
      have small : 2*k.val<n := by have := k.isLt; omega
      simp [natIx,evenPin,Nat.mod_eq_of_lt small,k.isLt]
  refine ⟨u,?_⟩; intro i
  have H := (shown (-u+i)).trans (pins _)
  simp only [add_neg_cancel_left] at H
  rw [H]
  constructor
  · rintro ⟨l,hl⟩; refine ⟨l,?_⟩; rw [ix_add,←hl]; simp
  · rintro ⟨l,hl⟩; refine ⟨l,?_⟩; rw [hl,ix_add]; simp
end CyclePins

namespace CyclePins
open scoped Classical

def best (n h : Nat) := 2^(2*h-1)*Nat.fib (n-2*h+3)

theorem fib3 (x : Nat) : Nat.fib (x+4) ≤ 3*Nat.fib (x+2) := by
  have a := @Nat.fib_le_fib_succ (x+1)
  have b := @Nat.fib_add_two (x+1)
  have c := @Nat.fib_add_two (x+2)
  change Nat.fib (x+3)=Nat.fib (x+1)+Nat.fib (x+2) at b
  change Nat.fib (x+4)=Nat.fib (x+2)+Nat.fib (x+3) at c
  change Nat.fib (x+1) ≤ Nat.fib (x+2) at a
  omega

theorem grow {n r : Nat} (hr : 0<r) (hs : 2*(r+1)≤n) :
    4*best n r ≤ 3*best n (r+1) := by
  let x:=n-2*(r+1)+1
  have a : n-2*r+3=x+4 := by dsimp [x]; omega
  have b : n-2*(r+1)+3=x+2 := by dsimp [x]
  have e : 2*(r+1)-1=(2*r-1)+2 := by omega
  simp only [best,a,b,e,pow_add]
  have H := Nat.mul_le_mul_left (2^(2*r-1)) (fib3 x)
  nlinarith only [H]

theorem growth {n r h : Nat} (hr : 0<r) (hs : r≤h) (hn : 2*h≤n) :
    best n r ≤ best n h := by
  induction h,hs using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have A := ih (by omega)
    have B := grow (by omega : 0<k) hn
    omega

theorem emptyLoss (n h : Nat) (hn : 2≤n) (hp : 1≤h) (hs : 2*h≤n) :
    64*Nat.fib (n+2) ≤ 63*best n h := by
  have first := growth (n:=n) (by omega : 0<1) hp hs
  have v : best n 1=2*Nat.fib (n+1) := by
    unfold best
    rw [show n-2*1+3=n+1 by omega]
    rfl
  rw [v] at first
  obtain ⟨a,ha⟩ : ∃ a, n=a+2 := ⟨n-2,by omega⟩
  subst n
  have f := @Nat.fib_add_two a
  have g := @Nat.fib_add_two (a+1)
  have j := @Nat.fib_add_two (a+2)
  have b := @Nat.fib_le_fib_succ a
  change Nat.fib (a+3)=Nat.fib (a+1)+Nat.fib (a+2) at g
  change Nat.fib (a+4)=Nat.fib (a+2)+Nat.fib (a+3) at j
  change 64*Nat.fib (a+4) ≤ _
  change 2*Nat.fib (a+3) ≤ _ at first
  omega

variable {n : Nat} [NeZero n]

theorem adjacentChoice (hn : 6≤n) (t k : Fin n) (ne : k≠t) :
    ∃ s : Fin n, (graph n).Adj t s ∧ s≠k ∧ ¬(graph n).Adj s k := by
  have apart (i : Fin n) (d : Nat) (hp : 0<d) (hb : d<n) : i+natIx d≠i := by
    intro eq
    have zero := add_eq_left.mp eq
    have v := congrArg Fin.val zero
    change d % n=0 at v; rw [Nat.mod_eq_of_lt hb] at v; omega
  have A := apart t 1 (by omega) (by omega)
  change t+1≠t at A
  have plus (x : Fin n) : x+1≠x := apart x 1 (by omega) (by omega)
  have step (d : Nat) : natIx (1+d) = (1:Fin n)+natIx d := by
    have v : (1:Fin n).val=1 := by change 1 % n=1; exact Nat.mod_eq_of_lt (by omega)
    simpa only [v] using (ix_add (1:Fin n) d)
  have c2 : natIx 2 = (1:Fin n)+1 := step 1
  have c3 : natIx 3 = (1:Fin n)+(1+1) := (step 2).trans (congrArg _ c2)
  have c4 : natIx 4 = (1:Fin n)+(1+(1+1)) := (step 3).trans (congrArg _ c3)
  by_cases bad : k=t+1 ∨ k=(t+1)+1
  · refine ⟨t-1,⟨?_,Or.inr (by simp)⟩,?_,?_⟩
    · intro e; have h:=congrArg (fun x : Fin n => x+1) e; simp at h; omega
    · intro e
      rcases bad with rfl|rfl
      · have h:=congrArg (fun x : Fin n => x+1) e
        have u : (t+1)+1=t := by simpa using h.symm
        apply apart t 2 (by omega) (by omega)
        simpa only [add_assoc,c2,c3,c4] using u
      · have h:=congrArg (fun x : Fin n => x+1) e
        have u : ((t+1)+1)+1=t := by simpa using h.symm
        apply apart t 3 (by omega) (by omega)
        simpa only [add_assoc,c2,c3,c4] using u
    · intro adj
      rcases adj.2 with b | b
      · exact ne (by simpa using b)
      · have h := congrArg (fun x : Fin n => x+1) b
        rcases bad with rfl|rfl
        · have u : ((t+1)+1)+1=t := by simpa using h.symm
          apply apart t 3 (by omega) (by omega)
          simpa only [add_assoc,c2,c3,c4] using u
        · have u : (((t+1)+1)+1)+1=t := by simpa using h.symm
          apply apart t 4 (by omega) (by omega)
          simpa only [add_assoc,c2,c3,c4] using u
  · push Not at bad
    exact ⟨t+1,⟨Ne.symm A,Or.inl rfl⟩,Ne.symm bad.1,fun h => h.2.elim bad.2
      (fun e => ne (add_right_cancel e).symm)⟩

theorem neighSmall (i : Fin n) : ((graph n).neighborFinset i).card≤2 := by
  have sub : (graph n).neighborFinset i ⊆ {i-1,i+1} := by
    intro j hj; have h := ((graph n).mem_neighborFinset i j).mp hj
    rcases h.2 with rfl|e
    · simp
    · have eq : j=i-1 := by rw [e]; simp
      simp [eq]
  have a := Finset.card_le_card sub
  have b := Finset.card_insert_le (i-1) ({i+1}:Finset (Fin n))
  simp only [Finset.card_singleton] at b
  omega

theorem separatePins {a h : Nat} [NeZero (2*a)] (ha : 3≤a) (j : Fin (2*a)) (T : Finset (Fin (2*a)))
    (coords : ∀ i : Fin (2*a), i∈T ↔ ∃ k : Fin h, i=natIx (j.val+2*k.val))
    (t s : Fin (2*a)) (mem : t∈T) (adj : (graph (2*a)).Adj t s) : s∉T := by
  have parity (i : Fin (2*a)) (hi : i∈T) : i.val % 2=j.val % 2 := by
    obtain ⟨k,rfl⟩ := (coords i).mp hi
    change ((j.val+2*k.val) % (2*a)) % 2=j.val % 2
    rw [Nat.mod_mod_of_dvd _ (by simp)]
    omega
  have step (i : Fin (2*a)) : (i+1).val % 2=(i.val+1) % 2 := by
    rw [Fin.val_add]
    have e : (1:Fin (2*a)).val=1 := by change 1 % (2*a)=1; exact Nat.mod_eq_of_lt (by omega)
    rw [e,Nat.mod_mod_of_dvd _ (by simp)]
  intro hs
  have pt:=parity _ mem; have ps:=parity _ hs
  rcases adj.2 with rfl|rfl <;> rw [step] at * <;> omega

end CyclePins

namespace Projection
open scoped Classical
open PinBasis (F Separates erase dot)
variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Allowed (G : SimpleGraph I) (D : Submodule F (I→F)) :=
  {w : I → F // (∀ i j, G.Adj i j → w i*w j=0) ∧ ∀ z∈D, dot w z=0}

def take {G : SimpleGraph I} {D : Submodule F (I→F)} (T : Finset I)
    (w : Allowed G D) : {y : I → F // LocalLoss.OK G T y} :=
  ⟨erase T w.val,fun i hi => by simp [erase,hi],by
    intro i j E
    by_cases a : i∈T <;> by_cases b : j∈T <;> simp [erase,a,b,w.property.1 i j E]⟩

theorem inj {G : SimpleGraph I} {D : Submodule F (I→F)} {T : Finset I}
    (b : T → D) (rows : ∀ t i : T, (b t).val i.val = if i=t then 1 else 0) :
    Function.Injective (take (G:=G) (D:=D) T) := by
  intro x y eq
  have hv : erase T x.val=erase T y.val := congrArg Subtype.val eq
  apply Subtype.ext; funext i
  by_cases h : i∈T
  · have A:=PinBasis.recover b rows _ x.property.2 ⟨i,h⟩
    have B:=PinBasis.recover b rows _ y.property.2 ⟨i,h⟩
    simpa only [hv,B] using A
  · simpa [erase,h] using congrFun hv i

theorem bound {G : SimpleGraph I} {D : Submodule F (I→F)} {T : Finset I}
    (b : T → D) (rows : ∀ t i : T, (b t).val i.val = if i=t then 1 else 0) :
    Nat.card (Allowed G D) ≤ Nat.card {y : I→F // LocalLoss.OK G T y} :=
  Nat.card_le_card_of_injective _ (inj b rows)

def form (z : I → F) : (I → F) →ₗ[F] F where
  toFun w := -dot w z
  map_add' x y := by simp [dot,add_mul,Finset.sum_add_distrib,add_comm]
  map_smul' c w := by simp [dot,Finset.mul_sum,mul_assoc]

theorem coeff (z : I→F) (k : I) : form z (Pi.single k 1) = -z k := by
  classical
  simp [form,dot,Pi.single_apply,ite_mul]

theorem supported {D : Submodule F (I→F)} {T : Finset I} (b : T→D) (sep : Separates D T)
    (rows : ∀ t i : T, (b t).val i.val = if i=t then 1 else 0)
    (coord : ∀ t : T, ∀ k∉T, (b t).val k=0) :
    ∀ z : I → F, z∈D ↔ ∀ i∉T, z i=0 := by
  classical
  intro z
  let v : D := ∑ t : T, z t.val • b t
  have sums (i : I) : v.val i = ∑ t : T, z t.val * (b t).val i := by
    simp [v,Submodule.coe_sum,Finset.sum_apply,smul_eq_mul]
  have matchT (i : I) (hi : i∈T) : v.val i = z i := by
    rw [sums,Finset.sum_eq_single_of_mem (⟨i,hi⟩:T) (Finset.mem_univ _)]; swap
    · intro t _ ne
      have e := rows t ⟨i,hi⟩
      simp only [if_neg (Ne.symm ne)] at e
      simp [e]
    · have e := rows (⟨i,hi⟩:T) ⟨i,hi⟩
      simpa using congrArg (fun q : F => z i*q) (by simpa using e : (b ⟨i,hi⟩).val i=1)
  have outside (i : I) (hi : i∉T) : v.val i=0 := by
    rw [sums]; apply Finset.sum_eq_zero; intro t _; rw [coord _ _ hi,mul_zero]
  constructor
  · intro hz
    have H : z-v.val=0 := sep _ (D.sub_mem hz v.property) (fun i hi => sub_eq_zero.mpr (matchT i hi).symm)
    rw [sub_eq_zero.mp H]; exact outside
  · intro hz
    have E : v.val=z := by
      funext i; by_cases hi : i∈T
      · exact matchT i hi
      · rw [outside i hi,hz i hi]
    rw [←E]; exact v.property

theorem loss {G : SimpleGraph I} {D : Submodule F (I→F)} {T : Finset I}
    [DecidableRel G.Adj] (b : T → D)
    (rows : ∀ t i : T, (b t).val i.val = if i=t then 1 else 0)
    (t : T) (k s : I) (ks : (b t).val k≠0) (kfree : k∉T) (sfree : s∉T)
    (near : G.Adj t.val s) (distant : ¬ G.Adj s k) (sk : s≠k)
    (degree : ∀ i, (G.neighborFinset i).card≤2) :
    32*Nat.card (Allowed G D) ≤ 31*Nat.card {y : I→F // LocalLoss.OK G T y} := by
  classical
  let M := ((G.neighborFinset s).erase t.val ∪ G.neighborFinset k) ∪ {s,k}
  have sm : s∈M := by simp [M]
  have km : k∈M := by simp [M]
  have arr := (G.mem_neighborFinset s t.val).mpr near.symm
  have c1 := Finset.card_union_le ((G.neighborFinset s).erase t.val) (G.neighborFinset k)
  have c2 := Finset.card_union_le ((G.neighborFinset s).erase t.val ∪ G.neighborFinset k) ({s,k}:Finset I)
  have c3 := Finset.card_insert_le s ({k}:Finset I)
  rw [Finset.card_erase_of_mem arr] at c1
  rw [Finset.card_singleton] at c3
  have small : M.card≤5 := by dsimp [M]; have := degree s; have := degree k; omega
  have safe (i : I) (a : i=s ∨ i=k) (j : I) (e : G.Adj i j) :
      j∈T ∨ (j∈M ∧ j≠s ∧ j≠k) := by
    by_cases hit : j=t.val
    · left; simpa [hit] using t.property
    right
    rcases a with rfl|rfl
    · exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hit,(G.mem_neighborFinset _ _).mpr e⟩)),
        e.ne.symm,fun h => distant (h ▸ e)⟩
    · exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr e)),
        fun h => distant (h ▸ e.symm),e.ne.symm⟩
  let L := form (b t).val
  have coef : L (Pi.single k 1)≠0 := by simpa [L,coeff] using ks
  have A:=LocalLoss.editLoss G T M s k L sm km sk sfree kfree small safe coef
  let embed (w : Allowed G D) : {y : I→F // LocalLoss.OK G T y ∧ y s*L y=0} :=
    ⟨(take T w).val,(take T w).property,by
      have e:=PinBasis.recover b rows _ w.property.2 t
      change erase T w.val s * (-dot (erase T w.val) (b t).val)=0
      rw [←e]
      simpa [erase,sfree] using w.property.1 s t.val near.symm⟩
  have J : Function.Injective embed := by
    intro x y h
    apply inj b rows
    have eq := congrArg (fun v : {y : I→F // LocalLoss.OK G T y ∧ y s*L y=0} => v.val) h
    exact Subtype.ext eq
  exact le_trans (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective embed J)) A

end Projection

namespace CyclePins
open scoped Classical

theorem withoutPins {n : Nat} [NeZero n] (hn : 1<n) :
    Nat.card {y : W n // LocalLoss.OK (graph n) ∅ y} ≤ Nat.fib (n+2) := by
  let send (w : {y : W n // LocalLoss.OK (graph n) ∅ y}) : Words n noPin 0 :=
    ⟨w.val,by
      have c := (grCycle hn w.val).mp w.property.2
      refine ⟨fun _ h => False.elim h,by simp,?_⟩
      intro i j e
      have one : (1:Fin n).val=1 := by change 1%n=1; exact Nat.mod_eq_of_lt hn
      have E : i+1=j := by
        apply Fin.ext; rw [Fin.val_add,one,←e,Nat.mod_eq_of_lt j.isLt]
      simpa only [E] using c i⟩
  rw [←pathCount]
  exact Nat.card_le_card_of_injective send (fun x y e => Subtype.ext (congrArg (fun z : Words n noPin 0 => z.val) e))

theorem negative {a h : Nat} [NeZero (2*a)] (ha : 3≤a) (hh : 1≤h) (hle : h≤a)
    (D : Submodule F (W (2*a))) (dim : Module.finrank F D≤h)
    (notBlock : ¬∃ j : Fin (2*a), ∀ z : W (2*a), z∈D ↔ ∀ i : Fin (2*a),
      (¬∃ k : Fin h, i=natIx (j.val+2*k.val)) → z i=0) :
    64*(2^Module.finrank F D * Nat.card (Projection.Allowed (graph (2*a)) D)) ≤
      63*best (2*a) h := by
  classical
  let n:=2*a
  let G:=graph (2*a)
  have big : 6≤2*a := by omega
  obtain ⟨T,b,sep,rank,rows⟩ := PinBasis.pivots D
  rw [←rank]
  have order : T.card≤h := rank.le.trans dim
  have ub:=Projection.bound (G:=G) b rows
  by_cases empty : T=∅
  · subst T
    simp only [Finset.card_empty,pow_zero,one_mul]
    have c:=withoutPins (n:=2*a) (by omega)
    have e:=emptyLoss (2*a) h (by omega) hh (by omega)
    exact (Nat.mul_le_mul_left 64 (ub.trans c)).trans e
  obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have pr : 0<T.card := Finset.card_pos.mpr ⟨j,hj⟩
  obtain ⟨xs,card,sum,A,sh⟩ := chart (by omega : 1<2*a) T j hj (by omega)
  have S := GapProducts.bound xs (by omega) (by omega)
  have cap : 2^T.card * GapProducts.cap xs = best (2*a) T.card := by
    unfold GapProducts.cap best
    rw [←Nat.mul_assoc,←pow_add,card]
    rw [show T.card+(T.card-1)=2*T.card-1 by omega,
      show xs.sum-T.card+3=2*a-2*T.card+3 by omega]
  let H:=Nat.card (Projection.Allowed G D)
  let mass:=GapProducts.mass xs
  change H ≤ _ at ub
  rw [A] at ub
  change H ≤ mass at ub
  change 64*(2^T.card*H) ≤ _
  have maxMass : 2^T.card*mass ≤ best (2*a) T.card :=
    (Nat.mul_le_mul_left _ S.1).trans_eq cap
  have maxH := (Nat.mul_le_mul_left (2^T.card) ub).trans maxMass
  by_cases full : T.card=h
  case neg =>
    have gap:=grow (n:=2*a) pr (by omega)
    have last:=growth (n:=2*a) (by omega : 0<T.card+1) (by omega : T.card+1≤h) (by omega)
    omega
  subst h
  by_cases atyp : 2≤GapProducts.bad xs
  · have q := Nat.mul_le_mul_left (2^T.card) (S.2 atyp)
    change 2^T.card*(26*mass) ≤ 2^T.card*(25*GapProducts.cap xs) at q
    rw [Nat.mul_left_comm (2^T.card) 26,Nat.mul_left_comm (2^T.card) 25,cap] at q
    have h1:=Nat.mul_le_mul_left (2^T.card) ub
    omega
  obtain ⟨u,hT⟩ := sh (by omega)
  have defect : ∃ t : T, ∃ k∉T, (b t).val k ≠ 0 := by
    by_contra! H
    apply notBlock; refine ⟨u,?_⟩
    intro z
    simpa only [←hT] using Projection.supported b sep rows H z
  obtain ⟨t,k,kfree,coef⟩ := defect
  have kt : k≠t.val := fun e => kfree (e ▸ t.property)
  obtain ⟨s,near,sk,far⟩ := adjacentChoice big t.val k kt
  have sfree := separatePins ha u T hT t.val s t.property near
  have loss := Projection.loss b rows t k s coef kfree sfree near far sk (fun i => neighSmall i)
  rw [A] at loss
  change 32*H≤31*mass at loss
  have scaled:=Nat.mul_le_mul_left (2^T.card) loss
  rw [Nat.mul_left_comm (2^T.card) 32,Nat.mul_left_comm (2^T.card) 31] at scaled
  omega

theorem cardinal {n : Nat} [NeZero n] (hn : 1<n) (D : Submodule F (W n)) :
    Nat.card {w : W n // (∀ i, w i*w (natIx (i.val+1))=0) ∧
      ∀ z∈D, (∑ i, w i*z i)=0} = Nat.card (Projection.Allowed (graph n) D) := by
  apply Nat.card_congr
  refine (Equiv.refl (W n)).subtypeEquiv ?_
  intro w; simp only [Equiv.refl_apply,grCycle hn,ix_succ]
  rfl

end CyclePins

end PEqualNP.Outside.L_lib_1022

theorem PEqualNP.Outside.L_lib_1022 : ∀ (a : ℕ) (ha : 0 < a) (h : ℕ), 3 ≤ a → 1 ≤ h → h ≤ a →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 2*a
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 1) ha)⟩ : Fin n)
  let even := fun (w : W) (i : Fin n) => if i.val % 2 = 0 then w i else 0
  let pin := fun (j : Fin n) (w : W) =>
    ∀ i : Fin n, (¬ ∃ k : Fin h, i = ix (j.val+2*k.val)) → w i = 0
  let best := 2^(2*h-1)*Nat.fib (n-2*h+3)
  ∀ D : Submodule F W, (∀ z ∈ D, even z ∈ D) → Module.finrank F D ≤ h →
    let hits := 2^(Module.finrank F D) * Nat.card {w : W //
      (∀ i, w i*w (ix (i.val+1)) = 0) ∧ (∀ z ∈ D, (∑ i, w i*z i) = 0)}
    let block := ∃ j : Fin n, ∀ z : W, z ∈ D ↔ pin j z
    (block → hits = best) ∧ (¬ block → 64*hits ≤ 63*best) := by
  intro a ha h ha3 hh hle
  letI : NeZero (2*a) := ⟨by omega⟩
  dsimp only
  intro D invariant dimension
  constructor
  · exact PEqualNP.Outside.L_lib_1022.CyclePins.positive a ha h ha3 hh hle D invariant dimension
  · intro notBlock
    have B := PEqualNP.Outside.L_lib_1022.CyclePins.negative ha3 hh hle D dimension notBlock
    rw [←PEqualNP.Outside.L_lib_1022.CyclePins.cardinal (by omega : 1<2*a) D] at B
    exact B
