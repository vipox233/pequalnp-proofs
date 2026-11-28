import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33639_aux
namespace Stable

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

lemma cycleStability : ∀ (a : ℕ) (ha : 0 < a) (h : ℕ), 3 ≤ a → 1 ≤ h → h ≤ a →
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
  · exact CyclePins.positive a ha h ha3 hh hle D invariant dimension
  · intro notBlock
    have B := CyclePins.negative ha3 hh hle D dimension notBlock
    rw [←CyclePins.cardinal (by omega : 1<2*a) D] at B
    exact B

end Stable


def ix (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def rot (n : ℕ) (hn : 0 < n) (s : ℕ) (w : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  w (ix n hn (i.val + n - s % n))

def out (n : ℕ) (hn : 0 < n) (name c raw : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  let old := rot n hn 3 raw + name
  let y := fun j : Fin n => old j + old (ix n hn (j.val+2)) + old (ix n hn (j.val+n-2))
  y i + (1+y (ix n hn (i.val+1)))*y (ix n hn (i.val+2)) + rot n hn 4 raw i + c i

noncomputable def run (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)

noncomputable def base (n : ℕ) (j : Fin 4) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0

noncomputable def even (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = 0 then z i else 0

def mix (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  let old := rot n hn 3 w
  old i + old (ix n hn (i.val+2)) + old (ix n hn (i.val+n-2))

noncomputable def tw (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (z : Fin n → ZMod 2) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.ofFn (fun i : Fin n =>
    let s : ℤ := if z i = 0 then 1 else -1
    let a : ℤ := if mark (ix n hn (i.val+n-2)) then 0 else s
    (!![1,s;1,a] : Matrix (Fin 2) (Fin 2) ℤ))).prod.trace

noncomputable def Ssum (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D), tw n hn mark z

def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

def dot (n : ℕ) (z x : Fin n → ZMod 2) : ZMod 2 := ∑ i, z i * x i

def adm (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (x : Fin n → ZMod 2) : Prop :=
  ∀ i, mark i = true → x (ix n hn (i.val+1)) * x (ix n hn (i.val+2)) = 0

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_sub (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma fn_sub (n : ℕ) (a b : Fin n → ZMod 2) : a - b = a + b := by
  funext i
  exact z2_sub (a i) (b i)

lemma fn_add_self (n : ℕ) (a : Fin n → ZMod 2) : a + a = 0 := by
  funext i
  exact z2_add_self (a i)

lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> decide

lemma ix_val (n : ℕ) (hn : 0 < n) (j : ℕ) : (ix n hn j).val = j % n := rfl

lemma ix_eq_iff (n : ℕ) (hn : 0 < n) (a b : ℕ) : ix n hn a = ix n hn b ↔ a % n = b % n := by
  simp [ix, Fin.ext_iff]

lemma ix_self (n : ℕ) (hn : 0 < n) (a : Fin n) : ix n hn a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_add_n (n : ℕ) (hn : 0 < n) (a : ℕ) : ix n hn (a + n) = ix n hn a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_val_add (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    ix n hn ((ix n hn a).val + b) = ix n hn (a + b) := by
  rw [ix_eq_iff]
  simp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma dot_comm (n : ℕ) (z x : Fin n → ZMod 2) : dot n z x = dot n x z := by
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma dot_add_left (n : ℕ) (z z' x : Fin n → ZMod 2) :
    dot n (z + z') x = dot n z x + dot n z' x := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply]; ring)

lemma dot_add_right (n : ℕ) (z x x' : Fin n → ZMod 2) :
    dot n z (x + x') = dot n z x + dot n z x' := by
  rw [dot_comm, dot_add_left, dot_comm n x z, dot_comm n x' z]

lemma dot_smul_left (n : ℕ) (a : ZMod 2) (z x : Fin n → ZMod 2) :
    dot n (a • z) x = a * dot n z x := by
  unfold dot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma dot_zero_left (n : ℕ) (x : Fin n → ZMod 2) : dot n 0 x = 0 := by
  unfold dot
  simp

lemma dot_zero_right (n : ℕ) (z : Fin n → ZMod 2) : dot n z 0 = 0 := by
  unfold dot
  simp

def dotL (n : ℕ) (x : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun z => dot n z x
    map_add' := fun z z' => dot_add_left n z z' x
    map_smul' := fun a z => dot_smul_left n a z x }

lemma dotL_apply (n : ℕ) (x z : Fin n → ZMod 2) : dotL n x z = dot n z x := rfl

lemma mix_add (n : ℕ) (hn : 0 < n) (w w' : Fin n → ZMod 2) :
    mix n hn (w + w') = mix n hn w + mix n hn w' := by
  funext i
  simp only [mix, rot, Pi.add_apply]
  ring

lemma mix_smul (n : ℕ) (hn : 0 < n) (a : ZMod 2) (w : Fin n → ZMod 2) :
    mix n hn (a • w) = a • mix n hn w := by
  funext i
  simp only [mix, rot, Pi.smul_apply, smul_eq_mul]
  ring

def mixL (n : ℕ) (hn : 0 < n) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := mix n hn
    map_add' := mix_add n hn
    map_smul' := mix_smul n hn }

lemma mixL_apply (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) : mixL n hn w = mix n hn w := rfl

lemma mix_zero (n : ℕ) (hn : 0 < n) : mix n hn 0 = 0 := (mixL n hn).map_zero

lemma mix_sub (n : ℕ) (hn : 0 < n) (w w' : Fin n → ZMod 2) :
    mix n hn (w - w') = mix n hn w - mix n hn w' := (mixL n hn).map_sub w w'

lemma even_apply (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) :
    even n z i = if i.val % 2 = 0 then z i else 0 := by
  unfold even
  split_ifs <;> rfl

lemma even_add (n : ℕ) (z z' : Fin n → ZMod 2) : even n (z + z') = even n z + even n z' := by
  funext i
  simp only [even_apply, Pi.add_apply]
  split_ifs <;> simp

lemma even_smul (n : ℕ) (a : ZMod 2) (z : Fin n → ZMod 2) : even n (a • z) = a • even n z := by
  funext i
  simp only [even_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

noncomputable def evenL (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := even n
    map_add' := even_add n
    map_smul' := even_smul n }

lemma evenL_apply (n : ℕ) (z : Fin n → ZMod 2) : evenL n z = even n z := rfl

lemma even_zero (n : ℕ) : even n 0 = 0 := (evenL n).map_zero

lemma even_even (n : ℕ) (z : Fin n → ZMod 2) : even n (even n z) = even n z := by
  funext i
  simp only [even_apply]
  split_ifs <;> rfl

lemma dot_even (n : ℕ) (z x : Fin n → ZMod 2) : dot n (even n z) x = dot n z (even n x) := by
  unfold dot
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [even_apply]
  split_ifs <;> simp

lemma base_apply (n : ℕ) (j : Fin 4) (i : Fin n) :
    base n j i = if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : ZMod 2) else 0 := by
  unfold base
  split_ifs <;> rfl

noncomputable def orth (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (LinearMap.pi (fun u : U => dotL n (τ u)))

lemma mem_orth (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) (z : Fin n → ZMod 2) :
    z ∈ orth n τ ↔ ∀ u, dot n z (τ u) = 0 := by
  unfold orth
  rw [LinearMap.mem_ker]
  constructor
  · intro hz u
    have := congrFun hz u
    simpa [dotL_apply] using this
  · intro hz
    funext u
    simpa [dotL_apply] using hz u

lemma Ssum_eq (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) [DecidablePred (fun z => z ∈ D)] :
    Ssum n hn mark D = ∑ z : Fin n → ZMod 2, if z ∈ D then tw n hn mark z else 0 := by
  unfold Ssum
  rw [Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun z _ => ?_)
  · congr
    funext a b
    exact Subsingleton.elim _ _
  · split_ifs <;> rfl

def h1_pw : (m : ℕ) → (Fin m → Matrix (Fin 2) (Fin 2) ℤ) → Fin 2 → (Fin m → Fin 2) → ℤ
  | 0, _, _, _ => 1
  | m + 1, A, u, x => A 0 u (x 0) * h1_pw m (fun i => A i.succ) (x 0) (fun i => x i.succ)

def h1_last : (m : ℕ) → Fin 2 → (Fin m → Fin 2) → Fin 2
  | 0, u, _ => u
  | m + 1, _, x => h1_last m (x 0) (fun i => x i.succ)

lemma h1_path [DecidableEq (Fin 2)] (m : ℕ) :
    ∀ (A : Fin m → Matrix (Fin 2) (Fin 2) ℤ) (u v : Fin 2),
    (List.ofFn A).prod u v =
      ∑ x : Fin m → Fin 2, if h1_last m u x = v then h1_pw m A u x else 0 := by
  induction m with
  | zero =>
    intro A u v
    rw [List.ofFn_zero, List.prod_nil, Matrix.one_apply, Fintype.sum_unique]
    rfl
  | succ m ih =>
    intro A u v
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [Fin.consEquiv_apply, h1_pw, h1_last, Fin.cons_zero, Fin.cons_succ]
    split_ifs <;> simp

lemma h1_last_succ (m : ℕ) : ∀ (u : Fin 2) (x : Fin (m + 1) → Fin 2),
    h1_last (m + 1) u x = x (Fin.last m) := by
  induction m with
  | zero =>
    intro u x
    rfl
  | succ m ih =>
    intro u x
    rw [h1_last, ih, Fin.succ_last]

lemma h1_pw_eq (m : ℕ) : ∀ (A : Fin m → Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2)
    (x p : Fin m → Fin 2), (∀ i : Fin m, i.val = 0 → p i = u) →
    (∀ i j : Fin m, i.val = j.val + 1 → p i = x j) →
    h1_pw m A u x = ∏ i, A i (p i) (x i) := by
  induction m with
  | zero =>
    intro A u x p _ _
    simp [h1_pw]
  | succ m ih =>
    intro A u x p h0 h1
    rw [h1_pw, Fin.prod_univ_succ, h0 0 rfl]
    congr 1
    exact ih (fun i => A i.succ) (x 0) (fun i => x i.succ) (fun i => p i.succ)
      (fun i hi => h1 i.succ 0 (by simp [hi])) (fun i j hij => h1 i.succ j.succ (by simp [hij]))

lemma h1_trace0 [DecidableEq (Fin 2)] (n : ℕ) (hn : 0 < n)
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℤ) :
    (List.ofFn A).prod.trace =
      ∑ x : Fin n → Fin 2, ∏ i, A i (x (ix n hn (i.val + n - 1))) (x i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, h1_path, h1_last_succ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  apply h1_pw_eq
  · intro i hi
    congr 1
    ext
    simp [ix, hi]
  · intro i j hij
    congr 1
    have hj : i.val + (m + 1) - 1 = j.val + (m + 1) := by omega
    rw [hj, ix_add_n, ix_self]

lemma h1_trace [DecidableEq (Fin 2)] (n : ℕ) (hn : 0 < n)
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℤ) :
    (List.ofFn A).prod.trace =
      ∑ x : Fin n → ZMod 2, ∏ i, A i (x (ix n hn (i.val + n - 1))) (x i) :=
  h1_trace0 n hn A

lemma h1_sgn_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

lemma h1_mat_apply (s a : ℤ) (u v : ZMod 2) :
    (!![1, s; 1, a] : Matrix (Fin 2) (Fin 2) ℤ) u v =
      if v = 0 then 1 else if u = 0 then s else a := by
  rcases z2_cases u with rfl | rfl <;> rcases z2_cases v with rfl | rfl <;> rfl

lemma h1_entry (P : Prop) [Decidable P] (zi : ZMod 2) [Decidable (zi = 0)] (u v : ZMod 2) :
    (!![1, (if zi = 0 then 1 else -1); 1, if P then 0 else (if zi = 0 then 1 else -1)] :
      Matrix (Fin 2) (Fin 2) ℤ) u v =
      if ¬ (P ∧ u = 1 ∧ v = 1) then sgn (zi * v) else 0 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [h1_mat_apply]
  by_cases hP : P <;> rcases z2_cases zi with rfl | rfl <;> rcases z2_cases u with rfl | rfl <;>
    rcases z2_cases v with rfl | rfl <;> simp [sgn, hP, h10]

lemma h1_f1 (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ix n hn ((ix n hn (i.val + 2)).val + n - 2) = i := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact Subsingleton.elim _ _
  · have e : (ix n hn (i.val + 2)).val + n - 2 = (ix n hn (i.val + 2)).val + (n - 2) := by omega
    have e2 : i.val + 2 + (n - 2) = i.val + n := by omega
    rw [e, ix_val_add, e2, ix_add_n, ix_self]

lemma h1_f2 (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ix n hn ((ix n hn (i.val + 2)).val + n - 1) = ix n hn (i.val + 1) := by
  have e : (ix n hn (i.val + 2)).val + n - 1 = (ix n hn (i.val + 2)).val + (n - 1) := by omega
  have e2 : i.val + 2 + (n - 1) = i.val + 1 + n := by omega
  rw [e, ix_val_add, e2, ix_add_n]

lemma h1_f3 (n : ℕ) (hn : 0 < n) (j : Fin n) :
    ix n hn ((ix n hn (j.val + n - 2)).val + 2) = j := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact Subsingleton.elim _ _
  · have e2 : j.val + n - 2 + 2 = j.val + n := by omega
    rw [ix_val_add, e2, ix_add_n, ix_self]

lemma h1_f4 (n : ℕ) (hn : 0 < n) (j : Fin n) :
    ix n hn ((ix n hn (j.val + n - 2)).val + 1) = ix n hn (j.val + n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact Subsingleton.elim _ _
  · have e2 : j.val + n - 2 + 1 = j.val + n - 1 := by omega
    rw [ix_val_add, e2]

lemma h1_adm_iff (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (x : Fin n → ZMod 2) :
    (∀ i : Fin n, ¬ (mark (ix n hn (i.val + n - 2)) = true ∧
      x (ix n hn (i.val + n - 1)) = 1 ∧ x i = 1)) ↔ adm n hn mark x := by
  constructor
  · intro H i hi
    have h := H (ix n hn (i.val + 2))
    rw [h1_f1, h1_f2] at h
    rcases z2_cases (x (ix n hn (i.val + 1))) with h1 | h1
    · rw [h1, zero_mul]
    · rcases z2_cases (x (ix n hn (i.val + 2))) with h2 | h2
      · rw [h2, mul_zero]
      · exact absurd ⟨hi, h1, h2⟩ h
  · rintro H j ⟨hm, h1, h2⟩
    have h := H (ix n hn (j.val + n - 2)) hm
    rw [h1_f3, h1_f4, h1, h2] at h
    exact absurd h (by decide)

open Classical in
lemma tw_eq_sum (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (z : Fin n → ZMod 2) :
    tw n hn mark z = ∑ x : Fin n → ZMod 2, if adm n hn mark x then sgn (dot n z x) else 0 := by
  unfold tw
  rw [@h1_trace (fun a b => Classical.propDecidable (a = b)) n hn]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [h1_entry]
  by_cases h : adm n hn mark x
  · rw [ite_eq_left h]
    have H := (h1_adm_iff n hn mark x).mpr h
    simp only [H, not_false_eq_true, ite_true]
    rw [← h1_sgn_sum]
    rfl
  · rw [ite_eq_right h]
    have H : ¬ ∀ i : Fin n, ¬ (mark (ix n hn (i.val + n - 2)) = true ∧
        x (ix n hn (i.val + n - 1)) = 1 ∧ x i = 1) :=
      fun h' => h ((h1_adm_iff n hn mark x).mp h')
    rw [not_forall] at H
    obtain ⟨i, hi⟩ := H
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, ite_false]

open Classical in
lemma h2_sum_sgn_linear {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (φ : V →ₗ[ZMod 2] ZMod 2) :
    (∑ x : V, sgn (φ x)) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with hφ
  · subst hφ
    simp [sgn_zero]
  · have hne : ∃ x0 : V, φ x0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    rcases hne with ⟨x0, hx0⟩
    have hx0_one : φ x0 = 1 := by
      rcases z2_cases (φ x0) with h | h
      · exact absurd h hx0
      · exact h
    have hx00 : x0 + x0 = 0 := by
      have h3 : (1 + 1 : ZMod 2) • x0 = x0 + x0 := by rw [add_smul, one_smul]
      rw [← h3, z2_add_self, zero_smul]
    have hbij : Function.Bijective (fun x : V => x + x0) :=
      ⟨fun x y h => by
        have := congrArg (fun z => z + x0) h
        simpa [add_assoc, hx00] using this,
       fun y => ⟨y + x0, by simp [add_assoc, hx00]⟩⟩
    have hshift : (∑ x : V, sgn (φ x)) = ∑ x : V, sgn (φ (x + x0)) :=
      (Fintype.sum_bijective (fun x => x + x0) hbij _ _ fun _ => rfl).symm
    have hneg : (∑ x : V, sgn (φ (x + x0))) = -(∑ x : V, sgn (φ x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h1 : sgn 1 = -1 := by decide
      rw [map_add, hx0_one, sgn_add, h1]
      ring
    linarith

lemma h2_dotL_eq_zero (n : ℕ) (v : Fin n → ZMod 2) : dotL n v = 0 ↔ v = 0 := by
  classical
  constructor
  · intro h
    funext i
    have h1 := LinearMap.congr_fun h (Pi.single i 1)
    rw [dotL_apply] at h1
    unfold dot at h1
    simpa [Pi.single_apply] using h1
  · intro h
    subst h
    refine LinearMap.ext (fun z => ?_)
    rw [dotL_apply, dot_zero_right]
    rfl

lemma h2_sum_sgn_dot (n : ℕ) (v : Fin n → ZMod 2) :
    (∑ z : Fin n → ZMod 2, sgn (dot n z v)) = if v = 0 then (2:ℤ)^n else 0 := by
  classical
  have h := h2_sum_sgn_linear (dotL n v)
  have h2 : ∀ z, sgn (dot n z v) = sgn (dotL n v z) := fun z => rfl
  rw [Finset.sum_congr rfl (fun z _ => h2 z), h]
  by_cases hv : v = 0
  · rw [ite_eq_left hv, ite_eq_left ((h2_dotL_eq_zero n v).mpr hv)]
    simp
  · rw [ite_eq_right hv, ite_eq_right (fun h' => hv ((h2_dotL_eq_zero n v).mp h'))]

open Classical in
lemma h2_sum_sgn_tau (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) (z : Fin n → ZMod 2) :
    (∑ u : U, sgn (dot n z (τ u))) = if z ∈ orth n τ then (Fintype.card U : ℤ) else 0 := by
  have h := h2_sum_sgn_linear ((dotL n z).comp τ)
  have h1 : ((dotL n z).comp τ = 0) ↔ z ∈ orth n τ := by
    rw [mem_orth]
    constructor
    · intro h0 u
      have h3 := LinearMap.congr_fun h0 u
      rw [LinearMap.comp_apply, dotL_apply, dot_comm] at h3
      exact h3
    · intro h0
      refine LinearMap.ext (fun u => ?_)
      rw [LinearMap.comp_apply, dotL_apply, dot_comm, h0 u]
      rfl
  have h2 : ∀ u, sgn (dot n z (τ u)) = sgn ((dotL n z).comp τ u) := fun u => by
    rw [LinearMap.comp_apply, dotL_apply, dot_comm]
  rw [Finset.sum_congr rfl (fun u _ => h2 u), h]
  by_cases hz : z ∈ orth n τ
  · rw [ite_eq_left hz, ite_eq_left (h1.mpr hz)]
  · rw [ite_eq_right hz, ite_eq_right (fun h' => hz (h1.mp h'))]

open Classical in
lemma h2_inversion (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (x : Fin n → ZMod 2) :
    (∑ z : Fin n → ZMod 2, tw n hn mark z * sgn (dot n z x)) =
      if adm n hn mark x then (2:ℤ)^n else 0 := by
  have h1 : ∀ z : Fin n → ZMod 2, tw n hn mark z * sgn (dot n z x) =
      ∑ x' : Fin n → ZMod 2, if adm n hn mark x' then sgn (dot n z (x' + x)) else 0 := by
    intro z
    rw [tw_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    split_ifs
    · rw [dot_add_right, sgn_add]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl (fun z _ => h1 z), Finset.sum_comm]
  have h2 : ∀ x' : Fin n → ZMod 2,
      (∑ z : Fin n → ZMod 2, if adm n hn mark x' then sgn (dot n z (x' + x)) else 0) =
        if x' = x then (if adm n hn mark x then (2:ℤ)^n else 0) else 0 := by
    intro x'
    by_cases ha : adm n hn mark x'
    · simp only [ite_eq_left ha]
      rw [h2_sum_sgn_dot]
      by_cases hx : x' = x
      · subst hx
        rw [ite_eq_left (fn_add_self n x'), ite_eq_left rfl, ite_eq_left ha]
      · rw [ite_eq_right hx, ite_eq_right]
        intro h0
        apply hx
        have h3 : x' = x' + x + x := by rw [add_assoc, fn_add_self, add_zero]
        rw [h3, h0, zero_add]
    · simp only [ite_eq_right ha, Finset.sum_const_zero]
      by_cases hx : x' = x
      · subst hx
        rw [ite_eq_left rfl, ite_eq_right ha]
      · rw [ite_eq_right hx]
  rw [Finset.sum_congr rfl (fun x' _ => h2 x')]
  simp

lemma fourier_count (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U] (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (2:ℤ)^n * (Nat.card {u : U // adm n hn mark (τ u)} : ℤ) =
      (Nat.card U : ℤ) * Ssum n hn mark (orth n τ) := by
  classical
  have := Fintype.ofFinite U
  rw [Ssum_eq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (2:ℤ)^n * ((Finset.univ.filter (fun u : U => adm n hn mark (τ u))).card : ℤ) =
      ∑ u : U, ∑ z : Fin n → ZMod 2, tw n hn mark z * sgn (dot n z (τ u)) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [h2_inversion]
    split_ifs <;> simp
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.mul_sum, h2_sum_sgn_tau]
  split_ifs <;> ring

lemma orth_card (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card U * Nat.card (orth n τ) = 2^n * Nat.card {u : U // τ u = 0} := by
  classical
  have := Fintype.ofFinite U
  have key : (Fintype.card U : ℤ) * (Fintype.card (orth n τ) : ℤ) =
      (2:ℤ)^n * (Fintype.card {u : U // τ u = 0} : ℤ) := by
    have e1 : (∑ z : Fin n → ZMod 2, ∑ u : U, sgn (dot n z (τ u))) =
        (Fintype.card U : ℤ) * (Fintype.card (orth n τ) : ℤ) := by
      rw [Finset.sum_congr rfl (fun z _ => h2_sum_sgn_tau n τ z)]
      rw [Fintype.card_of_subtype (Finset.univ.filter (fun z => z ∈ orth n τ)) (by simp)]
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      split_ifs <;> simp
    have e2 : (∑ z : Fin n → ZMod 2, ∑ u : U, sgn (dot n z (τ u))) =
        (2:ℤ)^n * (Fintype.card {u : U // τ u = 0} : ℤ) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun u _ => h2_sum_sgn_dot n (τ u))]
      rw [Fintype.card_of_subtype (Finset.univ.filter (fun u => τ u = 0)) (by simp)]
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      split_ifs <;> simp
    rw [← e1, e2]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast key

lemma h2_orth_card_subtype (n : ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card V * Nat.card (orth n V.subtype) = 2^n := by
  have h := orth_card n V.subtype
  have h1 : Nat.card {u : V // V.subtype u = 0} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, rfl⟩⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha := a.2
    have hb := b.2
    rw [Submodule.subtype_apply] at ha hb
    rw [ha, hb]
  rw [h, h1, mul_one]

lemma double_orth (n : ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (x : Fin n → ZMod 2)
    (hx : ∀ z, (∀ v ∈ V, dot n z v = 0) → dot n z x = 0) : x ∈ V := by
  classical
  have h1 : Nat.card V * Nat.card (orth n V.subtype) = 2^n :=
    h2_orth_card_subtype n V
  have h2 : Nat.card (orth n V.subtype) * Nat.card (orth n (orth n V.subtype).subtype) = 2^n :=
    h2_orth_card_subtype n (orth n V.subtype)
  have hpos : 0 < Nat.card (orth n V.subtype) := Nat.card_pos
  have h3 : Nat.card (orth n (orth n V.subtype).subtype) = Nat.card V := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h2, mul_comm, h1]
  have hle : V ≤ orth n (orth n V.subtype).subtype := by
    intro v hv
    rw [mem_orth]
    intro u
    have h4 := (mem_orth n V.subtype u.1).mp u.2 ⟨v, hv⟩
    rw [dot_comm]
    exact h4
  have heq : V = orth n (orth n V.subtype).subtype := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have c1 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)]
      simp
    have c2 : Nat.card (orth n (orth n V.subtype).subtype) =
        2 ^ Module.finrank (ZMod 2) (orth n (orth n V.subtype).subtype) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := orth n (orth n V.subtype).subtype)]
      simp
    rw [c1, c2] at h3
    exact le_of_eq (Nat.pow_right_injective (le_refl 2) h3)
  rw [heq, mem_orth]
  intro u
  rw [dot_comm]
  refine hx u.1 (fun v hv => ?_)
  exact (mem_orth n V.subtype u.1).mp u.2 ⟨v, hv⟩

lemma lane_pure_span (n h : ℕ) (B D : Submodule (ZMod 2) (Fin n → ZMod 2)) (hBD : B ≤ D)
    (hB : ∀ z ∈ B, even n z ∈ B) (hD : ∀ z ∈ D, even n z ∈ D)
    (hfin : Module.finrank (ZMod 2) D ≤ h + Module.finrank (ZMod 2) B) :
    ∃ v : Fin h → (Fin n → ZMod 2), (∀ j, even n (v j) = v j ∨ even n (v j) = 0) ∧
      (∀ j, v j ∈ D) ∧ D ≤ B ⊔ Submodule.span (ZMod 2) (Set.range v) := by
  induction h generalizing B with
  | zero =>
    have hEq : B = D := Submodule.eq_of_le_of_finrank_le hBD (by simpa using hfin)
    refine ⟨fun _ => 0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    rw [hEq]
    exact le_sup_left
  | succ h ih =>
    by_cases hEq : B = D
    · refine ⟨fun _ => 0, fun _ => Or.inl (even_zero n), fun _ => D.zero_mem, ?_⟩
      rw [hEq]
      exact le_sup_left
    · have hlt : B < D := lt_of_le_of_ne hBD hEq
      obtain ⟨z, hzD, hzB⟩ := IsConcreteLE.exists_of_lt hlt
      have hv0 : ∃ v0, v0 ∈ D ∧ v0 ∉ B ∧ (even n v0 = v0 ∨ even n v0 = 0) := by
        by_cases he : even n z ∈ B
        · refine ⟨z + even n z, D.add_mem hzD (hD z hzD), ?_, Or.inr ?_⟩
          · intro hmem
            apply hzB
            have h1 : z = (z + even n z) + even n z := by
              rw [add_assoc, fn_add_self, add_zero]
            rw [h1]
            exact B.add_mem hmem he
          · rw [even_add, even_even, fn_add_self]
        · exact ⟨even n z, hD z hzD, he, Or.inl (even_even n z)⟩
      obtain ⟨v0, hv0D, hv0B, hv0e⟩ := hv0
      have hv0span : v0 ∈ B ⊔ Submodule.span (ZMod 2) {v0} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self v0)
      have hB'D : B ⊔ Submodule.span (ZMod 2) {v0} ≤ D := by
        refine sup_le hBD ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hv0D
      have hB'even : ∀ w ∈ B ⊔ Submodule.span (ZMod 2) {v0},
          even n w ∈ B ⊔ Submodule.span (ZMod 2) {v0} := by
        intro w hw
        obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hc
        rw [even_add, even_smul]
        refine Submodule.add_mem _ (Submodule.mem_sup_left (hB b hb)) ?_
        refine Submodule.smul_mem _ _ ?_
        rcases hv0e with h1 | h1
        · rw [h1]
          exact hv0span
        · rw [h1]
          exact Submodule.zero_mem _
      have hlt' : B < B ⊔ Submodule.span (ZMod 2) {v0} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hv0B
        rw [heq]
        exact hv0span
      have hfr : Module.finrank (ZMod 2) B <
          Module.finrank (ZMod 2) (B ⊔ Submodule.span (ZMod 2) {v0} :
            Submodule (ZMod 2) (Fin n → ZMod 2)) :=
        Submodule.finrank_lt_finrank_of_lt hlt'
      obtain ⟨v', hv'e, hv'D, hv'span⟩ :=
        ih (B ⊔ Submodule.span (ZMod 2) {v0}) hB'D hB'even (by omega)
      refine ⟨fun j => Fin.cases v0 v' j, ?_, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa using hv0e
        · simpa using hv'e i
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa using hv0D
        · simpa using hv'D i
      · refine le_trans hv'span ?_
        refine sup_le (sup_le le_sup_left ?_) ?_
        · refine le_trans (Submodule.span_mono ?_) le_sup_right
          rintro _ rfl
          exact ⟨0, rfl⟩
        · refine le_trans (Submodule.span_mono ?_) le_sup_right
          rintro _ ⟨i, rfl⟩
          exact ⟨i.succ, rfl⟩

lemma h3_ix_shift (n : ℕ) (hn : 0 < n) (a s : ℕ) (hs : s ≤ n) :
    ix n hn ((ix n hn a).val + n - s) = ix n hn (a + (n - s)) := by
  have e : (ix n hn a).val + n - s = (ix n hn a).val + (n - s) := by omega
  rw [e, ix_val_add]

lemma h3_mix_apply (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2) (i : Fin n) :
    mix n hn w i = w (ix n hn (i.val + n - 3)) + w (ix n hn (i.val + n - 1)) +
      w (ix n hn (i.val + n - 5)) := by
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [mix, rot, h3]
  rw [h3_ix_shift n hn _ 3 (by omega), h3_ix_shift n hn _ 3 (by omega)]
  have e1 : i.val + 2 + (n - 3) = i.val + n - 1 := by omega
  have e2 : i.val + n - 2 + (n - 3) = i.val + n - 5 + n := by omega
  rw [e1, e2, ix_add_n]

lemma h3_mix_ix (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2) (a : ℕ) :
    mix n hn w (ix n hn (a + 5)) = w (ix n hn (a + 2)) + w (ix n hn (a + 4)) +
      w (ix n hn a) := by
  rw [h3_mix_apply n hn h6n, h3_ix_shift n hn _ 3 (by omega), h3_ix_shift n hn _ 1 (by omega),
    h3_ix_shift n hn _ 5 (by omega)]
  have e1 : a + 5 + (n - 3) = a + 2 + n := by omega
  have e2 : a + 5 + (n - 1) = a + 4 + n := by omega
  have e3 : a + 5 + (n - 5) = a + n := by omega
  rw [e1, e2, e3, ix_add_n, ix_add_n, ix_add_n]

lemma h3_z2_mid (x y z : ZMod 2) (h : x + y + z = 0) : y = x + z := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;>
    rcases z2_cases z with rfl | rfl <;> revert h <;> decide

lemma h3_ker_step (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2)
    (hw : mix n hn w = 0) (a : ℕ) :
    w (ix n hn (a + 4)) = w (ix n hn (a + 2)) + w (ix n hn a) := by
  have h := congrFun hw (ix n hn (a + 5))
  rw [h3_mix_ix n hn h6n] at h
  exact h3_z2_mid _ _ _ h

lemma h3_ker_agree (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w w' : Fin n → ZMod 2)
    (hw : mix n hn w = 0) (hw' : mix n hn w' = 0)
    (h4 : ∀ a : ℕ, a < 4 → w (ix n hn a) = w' (ix n hn a)) :
    ∀ m : ℕ, w (ix n hn m) = w' (ix n hn m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 4
    · exact h4 m hm
    · obtain ⟨a, rfl⟩ : ∃ a, m = a + 4 := ⟨m - 4, by omega⟩
      rw [h3_ker_step n hn h6n w hw a, h3_ker_step n hn h6n w' hw' a,
        ih (a + 2) (by omega), ih a (by omega)]

lemma ker_mix_card (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Nat.card {w : Fin n → ZMod 2 // mix n hn w = 0} ≤ 16 := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  have hinj : Function.Injective
      (fun (w : {w : Fin n → ZMod 2 // mix n hn w = 0}) (a : Fin 4) => w.1 (ix n hn a.val)) := by
    intro w w' hww
    apply Subtype.ext
    funext i
    have h4 : ∀ a : ℕ, a < 4 → w.1 (ix n hn a) = w'.1 (ix n hn a) := by
      intro a ha
      exact congrFun hww ⟨a, ha⟩
    have := h3_ker_agree n hn h6n w.1 w'.1 w.2 w'.2 h4 i.val
    rwa [ix_self] at this
  have hc := Nat.card_le_card_of_injective _ hinj
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rwa [h16] at hc

def h3_b (j : Fin 4) (q : ℕ) : ZMod 2 :=
  if q % 2 = j.val / 2 ∧ (q / 2 % 3 = j.val % 2 ∨ q / 2 % 3 = 2) then (1 : ZMod 2) else 0

lemma h3_b_mod (j : Fin 4) (q : ℕ) : h3_b j (q % 6) = h3_b j q := by
  have e1 : q % 6 % 2 = q % 2 := by omega
  have e2 : q % 6 / 2 % 3 = q / 2 % 3 := by omega
  unfold h3_b
  rw [e1, e2]

lemma h3_b_congr (j : Fin 4) (p q : ℕ) (h : p % 6 = q % 6) : h3_b j p = h3_b j q := by
  rw [← h3_b_mod j p, ← h3_b_mod j q, h]

lemma h3_base_ix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (j : Fin 4) (a : ℕ) :
    base n j (ix n hn a) = h3_b j a := by
  rw [base_apply, ix_val]
  exact h3_b_congr j (a % n) a (Nat.mod_mod_of_dvd a h6)

lemma h3_b_fin : ∀ (j : Fin 4) (r : Fin 6),
    h3_b j (r.val + 3) + h3_b j (r.val + 1) + h3_b j (r.val + 5) = 0 := by
  decide

lemma h3_b_sum (j : Fin 4) (a : ℕ) :
    h3_b j (a + 3) + h3_b j (a + 1) + h3_b j (a + 5) = 0 := by
  have h := h3_b_fin j ⟨a % 6, Nat.mod_lt _ (by norm_num)⟩
  rw [h3_b_congr j (a + 3) (a % 6 + 3) (by omega), h3_b_congr j (a + 1) (a % 6 + 1) (by omega),
    h3_b_congr j (a + 5) (a % 6 + 5) (by omega)]
  exact h

def h3_shift (n : ℕ) (hn : 0 < n) (s : ℕ) (hs : s ≤ n) : Fin n ≃ Fin n where
  toFun i := ix n hn (i.val + s)
  invFun i := ix n hn (i.val + n - s)
  left_inv i := by
    show ix n hn ((ix n hn (i.val + s)).val + n - s) = i
    rw [h3_ix_shift n hn _ s hs]
    have e : i.val + s + (n - s) = i.val + n := by omega
    rw [e, ix_add_n, ix_self]
  right_inv i := by
    show ix n hn ((ix n hn (i.val + n - s)).val + s) = i
    rw [ix_val_add]
    have e : i.val + n - s + s = i.val + n := by omega
    rw [e, ix_add_n, ix_self]

lemma h3_sum_shift (n : ℕ) (hn : 0 < n) (s : ℕ) (hs : s ≤ n) (f g : Fin n → ZMod 2) :
    ∑ i, f i * g (ix n hn (i.val + n - s)) = ∑ i, f (ix n hn (i.val + s)) * g i := by
  rw [← Equiv.sum_comp (h3_shift n hn s hs) (fun i => f i * g (ix n hn (i.val + n - s)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e : ix n hn (((h3_shift n hn s hs) i).val + n - s) = i :=
    (h3_shift n hn s hs).left_inv i
  rw [e]
  rfl

lemma base_dot_mix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (j : Fin 4) (w : Fin n → ZMod 2) :
    dot n (base n j) (mix n hn w) = 0 := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  unfold dot
  have e1 : ∀ i : Fin n, base n j i * mix n hn w i =
      base n j i * w (ix n hn (i.val + n - 3)) + base n j i * w (ix n hn (i.val + n - 1)) +
        base n j i * w (ix n hn (i.val + n - 5)) := by
    intro i
    rw [h3_mix_apply n hn h6n]
    ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    h3_sum_shift n hn 3 (by omega), h3_sum_shift n hn 1 (by omega),
    h3_sum_shift n hn 5 (by omega), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [h3_base_ix n hn h6, h3_base_ix n hn h6, h3_base_ix n hn h6, ← add_mul, ← add_mul,
    h3_b_sum, zero_mul]

lemma even_base (n : ℕ) (j : Fin 4) :
    even n (base n j) = base n j ∨ even n (base n j) = 0 := by
  by_cases hj : j.val / 2 = 0
  · left
    funext i
    rw [even_apply, base_apply]
    split_ifs with h1 h2 h2
    · rfl
    · rfl
    · exfalso
      omega
    · rfl
  · right
    funext i
    rw [even_apply, base_apply, Pi.zero_apply]
    split_ifs with h1 h2
    · exfalso
      omega
    · rfl
    · rfl

lemma h3_base_li (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    LinearIndependent (ZMod 2) (base n) := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ i : Fin n, g 0 * base n 0 i + g 1 * base n 1 i + g 2 * base n 2 i +
      g 3 * base n 3 i = 0 := by
    intro i
    have := congrFun hg i
    simpa [Fin.sum_univ_four] using this
  have h0 := key ⟨0, by omega⟩
  have h1 := key ⟨2, by omega⟩
  have h2 := key ⟨1, by omega⟩
  have h3 := key ⟨3, by omega⟩
  simp [base_apply] at h0 h1 h2 h3
  intro i
  fin_cases i <;> assumption

lemma base_span_finrank (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    4 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (base n))) := by
  rw [finrank_span_eq_card (h3_base_li n hn h6)]
  simp

lemma h3_span_le_orth (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Submodule.span (ZMod 2) (Set.range (base n)) ≤ orth n (mixL n hn) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_orth]
  intro u
  exact base_dot_mix n hn h6 j u

lemma h3_orth_card_le (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Nat.card (orth n (mixL n hn)) ≤ 16 := by
  have h := orth_card n (mixL n hn)
  have hW : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hk : Nat.card {u : Fin n → ZMod 2 // (mixL n hn) u = 0} ≤ 16 := ker_mix_card n hn h6
  rw [hW] at h
  have h2 : Nat.card (orth n (mixL n hn)) = Nat.card {u : Fin n → ZMod 2 // (mixL n hn) u = 0} :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by positivity)) h
  rw [h2]
  exact hk

lemma h3_orth_eq_span (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Submodule.span (ZMod 2) (Set.range (base n)) = orth n (mixL n hn) := by
  refine Submodule.eq_of_le_of_finrank_le (h3_span_le_orth n hn h6) ?_
  refine le_trans ?_ (base_span_finrank n hn h6)
  have hc := h3_orth_card_le n hn h6
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc

lemma mix_surj (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (x : Fin n → ZMod 2)
    (hx : ∀ j, dot n (base n j) x = 0) : ∃ w, mix n hn w = x := by
  have hB : Submodule.span (ZMod 2) (Set.range (base n)) ≤ LinearMap.ker (dotL n x) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, dotL_apply]
    exact hx j
  have hR : x ∈ LinearMap.range (mixL n hn) := by
    refine double_orth n _ x (fun z hz => ?_)
    have hzO : z ∈ orth n (mixL n hn) := by
      rw [mem_orth]
      intro u
      exact hz _ (LinearMap.mem_range_self _ u)
    rw [← h3_orth_eq_span n hn h6] at hzO
    have := hB hzO
    rwa [LinearMap.mem_ker, dotL_apply] at this
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hR
  exact ⟨w, hw⟩

def h4_bit (x : ZMod 2) : ℕ := if x = 0 then 0 else 1

lemma h4_bit_le (x : ZMod 2) : h4_bit x ≤ 1 := by
  unfold h4_bit
  split_ifs <;> omega

lemma h4_bit_eq_iff (x y : ZMod 2) : h4_bit x = h4_bit y ↔ x - y = 0 := by
  revert x y
  decide

lemma h4_run_succ (n h : ℕ) (ask : Fin (h+1) → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) :
    run n (h+1) ask w = 2 * run n h (fun j => ask j.castSucc) w +
      h4_bit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w) w) := by
  unfold run h4_bit
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  congr

lemma run_eq_iff (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w0 : Fin n → ZMod 2) :
    ∃ p : Fin h → ℕ, ∀ w, run n h ask w = run n h ask w0 ↔ ∀ j, ask j (p j) (w - w0) = 0 := by
  induction h with
  | zero =>
    refine ⟨fun _ => 0, fun w => ?_⟩
    constructor
    · intro _ j
      exact j.elim0
    · intro _
      rfl
  | succ h ih =>
    obtain ⟨p', hp'⟩ := ih (fun j => ask j.castSucc)
    refine ⟨@Fin.snoc h (fun _ => ℕ) p' (run n h (fun j => ask j.castSucc) w0), fun w => ?_⟩
    rw [h4_run_succ, h4_run_succ, Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hp' w]
    have hb1 := h4_bit_le (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w) w)
    have hb2 := h4_bit_le (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w0)
    constructor
    · intro he
      have h1 : run n h (fun j => ask j.castSucc) w = run n h (fun j => ask j.castSucc) w0 := by
        omega
      refine ⟨h1, ?_⟩
      rw [h1] at he
      have h2 : h4_bit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w) =
          h4_bit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w0) := by
        omega
      rw [h4_bit_eq_iff, ← map_sub] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      rw [h1]
      congr 1
      rw [h4_bit_eq_iff, ← map_sub]
      exact h2

lemma cell_structure (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w0 : Fin n → ZMod 2) :
    ∃ K : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ w, run n h ask w = run n h ask w0 ↔ w - w0 ∈ K) ∧ 2^n ≤ Nat.card K * 2^h := by
  obtain ⟨p, hp⟩ := run_eq_iff n h ask w0
  refine ⟨LinearMap.ker (LinearMap.pi (fun j => ask j (p j))), fun w => ?_, ?_⟩
  · rw [hp w, LinearMap.mem_ker]
    constructor
    · intro hj
      funext j
      exact hj j
    · intro hj j
      exact congrFun hj j
  · have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (fun j => ask j (p j)))
    have h2 : Module.finrank (ZMod 2)
        (LinearMap.range (LinearMap.pi (fun j => ask j (p j)))) ≤ h := by
      have h3 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (fun j => ask j (p j))))
      rwa [Module.finrank_fin_fun] at h3
    rw [Module.finrank_fin_fun] at h1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

def h5_m0 (n : ℕ) (hn : 0 < n) (name : Fin n → ZMod 2) (j : Fin n) : ZMod 2 :=
  name j + name (ix n hn (j.val+2)) + name (ix n hn (j.val+n-2))

def h5_L (n : ℕ) (hn : 0 < n) (name : Fin n → ZMod 2) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := fun w i => mix n hn w i + mix n hn w (ix n hn (i.val+2))
      + h5_m0 n hn name (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2))
      + h5_m0 n hn name (ix n hn (i.val+2)) * mix n hn w (ix n hn (i.val+1))
      + rot n hn 4 w i
    map_add' := fun w w' => by
      funext i
      simp only [mix_add, Pi.add_apply, rot]
      ring
    map_smul' := fun a w => by
      funext i
      simp only [mix_smul, Pi.smul_apply, smul_eq_mul, rot, RingHom.id_apply]
      ring }

lemma out_affine (n : ℕ) (hn : 0 < n) (name c : Fin n → ZMod 2) :
    ∃ (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (c0 : Fin n → ZMod 2),
      ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i =
        mix n hn w (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2)) + (L w + c0) i := by
  refine ⟨h5_L n hn name, fun i => h5_m0 n hn name i + h5_m0 n hn name (ix n hn (i.val+2))
    + h5_m0 n hn name (ix n hn (i.val+1)) * h5_m0 n hn name (ix n hn (i.val+2)) + c i,
    fun w i => ?_⟩
  simp only [out, h5_L, h5_m0, mix, rot, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ring

noncomputable def h5_KZ (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  K ⊓ Submodule.comap (mixL n hn) (LinearMap.ker (evenL n))

lemma h5_mem_KZ (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (x : Fin n → ZMod 2) : x ∈ h5_KZ n hn K ↔ x ∈ K ∧ even n (mix n hn x) = 0 := by
  unfold h5_KZ
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker, mixL_apply, evenL_apply]

lemma h5_odd_KZ (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (κ : ↥(h5_KZ n hn K)) : even n (mix n hn (κ : Fin n → ZMod 2)) = 0 :=
  ((h5_mem_KZ n hn K _).1 κ.2).2

noncomputable def h5_tau (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (↥K × ↥(h5_KZ n hn K)) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  ((evenL n).comp ((mixL n hn).comp K.subtype)).coprod
    ((mixL n hn).comp (h5_KZ n hn K).subtype)

lemma h5_tau_apply (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (u : ↥K × ↥(h5_KZ n hn K)) :
    h5_tau n hn K u =
      even n (mix n hn (u.1 : Fin n → ZMod 2)) + mix n hn (u.2 : Fin n → ZMod 2) := rfl

lemma h5_base_mem (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (j : Fin 4) :
    base n j ∈ orth n (h5_tau n hn K) := by
  rw [mem_orth]
  intro u
  rw [h5_tau_apply, dot_add_right, base_dot_mix n hn h6, add_zero, ← dot_even]
  rcases even_base n j with h | h
  · rw [h, base_dot_mix n hn h6]
  · rw [h, dot_zero_left]

lemma h5_even_mem (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (z : Fin n → ZMod 2) (hz : z ∈ orth n (h5_tau n hn K)) :
    even n z ∈ orth n (h5_tau n hn K) := by
  rw [mem_orth] at hz ⊢
  intro u
  have h := hz (u.1, 0)
  rw [h5_tau_apply] at h
  simp only [ZeroMemClass.coe_zero, mix_zero, add_zero] at h
  rw [h5_tau_apply, dot_even, even_add, even_even, h5_odd_KZ, add_zero]
  exact h

lemma h5_tau_zero (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (u : ↥K × ↥(h5_KZ n hn K)) (h : h5_tau n hn K u = 0) :
    even n (mix n hn (u.1 : Fin n → ZMod 2)) = 0 ∧ mix n hn (u.2 : Fin n → ZMod 2) = 0 := by
  rw [h5_tau_apply] at h
  have h1 := congrArg (even n) h
  rw [even_add, even_even, h5_odd_KZ, add_zero, even_zero] at h1
  rw [h1, zero_add] at h
  exact ⟨h1, h⟩

lemma h5_card_ker (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {u : ↥K × ↥(h5_KZ n hn K) // h5_tau n hn K u = 0} ≤
      Nat.card (h5_KZ n hn K) * 16 := by
  have h3 : Nat.card {u : ↥K × ↥(h5_KZ n hn K) // h5_tau n hn K u = 0} ≤
      Nat.card (↥(h5_KZ n hn K) × {w : Fin n → ZMod 2 // mix n hn w = 0}) := by
    refine Nat.card_le_card_of_injective (fun u =>
      (⟨(u.1.1 : Fin n → ZMod 2),
        (h5_mem_KZ n hn K _).2 ⟨u.1.1.2, (h5_tau_zero n hn K u.1 u.2).1⟩⟩,
       ⟨(u.1.2 : Fin n → ZMod 2), (h5_tau_zero n hn K u.1 u.2).2⟩)) ?_
    intro u v huv
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at huv
    exact Subtype.ext (Prod.ext (Subtype.ext huv.1) (Subtype.ext huv.2))
  rw [Nat.card_prod] at h3
  exact le_trans h3 (Nat.mul_le_mul_left _ (ker_mix_card n hn h6))

lemma h5_card_D (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card (orth n (h5_tau n hn K)) * Nat.card K ≤ 2^n * 16 := by
  have h1 := orth_card n (h5_tau n hn K)
  rw [Nat.card_prod] at h1
  have h2 := h5_card_ker n hn h6 K
  have hpos : 0 < Nat.card (h5_KZ n hn K) := Nat.card_pos
  have h4 : Nat.card (h5_KZ n hn K) * (Nat.card (orth n (h5_tau n hn K)) * Nat.card K) ≤
      Nat.card (h5_KZ n hn K) * (2^n * 16) := by
    calc Nat.card (h5_KZ n hn K) * (Nat.card (orth n (h5_tau n hn K)) * Nat.card K)
        = Nat.card K * Nat.card (h5_KZ n hn K) * Nat.card (orth n (h5_tau n hn K)) := by ring
      _ = 2^n * Nat.card {u : ↥K × ↥(h5_KZ n hn K) // h5_tau n hn K u = 0} := h1
      _ ≤ 2^n * (Nat.card (h5_KZ n hn K) * 16) := Nat.mul_le_mul_left _ h2
      _ = Nat.card (h5_KZ n hn K) * (2^n * 16) := by ring
  exact Nat.le_of_mul_le_mul_left h4 hpos

def h5_P (n : ℕ) (hn : 0 < n) (i : Fin n) (x : Fin n → ZMod 2) : ZMod 2 :=
  x (ix n hn (i.val+1)) * x (ix n hn (i.val+2))

def h5_g (n : ℕ) (hn : 0 < n) (i : Fin n) (x x' : Fin n → ZMod 2) : ZMod 2 :=
  x (ix n hn (i.val+1)) * x' (ix n hn (i.val+2)) + x' (ix n hn (i.val+1)) * x (ix n hn (i.val+2))

lemma h5_par (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) :
    ((ix n hn (i.val+1)).val % 2 = 0 ∧ (ix n hn (i.val+2)).val % 2 = 1) ∨
    ((ix n hn (i.val+1)).val % 2 = 1 ∧ (ix n hn (i.val+2)).val % 2 = 0) := by
  rw [ix_val, ix_val, Nat.mod_mod_of_dvd _ h2, Nat.mod_mod_of_dvd _ h2]
  omega

lemma h5_odd (n : ℕ) (x : Fin n → ZMod 2) (h : even n x = 0) (j : Fin n)
    (hj : j.val % 2 = 0) : x j = 0 := by
  have h1 := congrFun h j
  rw [even_apply] at h1
  split_ifs at h1
  exact h1

lemma h5_evn1 (n : ℕ) (x : Fin n → ZMod 2) (j : Fin n) (hj : j.val % 2 = 1) :
    even n x j = 0 := by
  rw [even_apply]
  split_ifs with h
  · omega
  · rfl

lemma h5_evn0 (n : ℕ) (x : Fin n → ZMod 2) (j : Fin n) (hj : j.val % 2 = 0) :
    even n x j = x j := by
  rw [even_apply]
  split_ifs
  rfl

lemma h5_P_add (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x' = 0) : h5_P n hn i (x + x') = h5_P n hn i x + h5_g n hn i x x' := by
  unfold h5_P h5_g
  simp only [Pi.add_apply]
  rcases h5_par n hn h2 i with ⟨ha, -⟩ | ⟨-, hb⟩
  · rw [h5_odd n x' h _ ha]
    ring
  · rw [h5_odd n x' h _ hb]
    ring

lemma h5_g_odd (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x = 0) (h' : even n x' = 0) : h5_g n hn i x x' = 0 := by
  unfold h5_g
  rcases h5_par n hn h2 i with ⟨ha, -⟩ | ⟨-, hb⟩
  · rw [h5_odd n x h _ ha, h5_odd n x' h' _ ha]
    ring
  · rw [h5_odd n x h _ hb, h5_odd n x' h' _ hb]
    ring

lemma h5_g_add (n : ℕ) (hn : 0 < n) (i : Fin n) (x y x' : Fin n → ZMod 2) :
    h5_g n hn i (x + y) x' = h5_g n hn i x x' + h5_g n hn i y x' := by
  unfold h5_g
  simp only [Pi.add_apply]
  ring

lemma h5_P_even (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x' = 0) : h5_P n hn i (even n x + x') = h5_g n hn i x x' := by
  unfold h5_P h5_g
  simp only [Pi.add_apply]
  rcases h5_par n hn h2 i with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [h5_odd n x' h _ ha, h5_evn0 n x _ ha, h5_evn1 n x _ hb]
    ring
  · rw [h5_odd n x' h _ hb, h5_evn1 n x _ ha, h5_evn0 n x _ hb]
    ring

lemma h5_fib (α β γ : Type) [Finite α] [Finite β] [Finite γ] (S : α → β → Prop)
    (T : α → γ → Prop) (h : ∀ a, Nat.card {b // S a b} ≤ Nat.card {c // T a c}) :
    Nat.card {p : α × β // S p.1 p.2} ≤ Nat.card {p : α × γ // T p.1 p.2} := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype S),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype T), Nat.card_sigma, Nat.card_sigma]
  exact Finset.sum_le_sum (fun a _ => h a)

lemma h5_fib2 (α β γ : Type) [Finite α] [Finite β] [Finite γ] (S : β → α → Prop)
    (T : γ → α → Prop) (h : ∀ a, Nat.card {b // S b a} ≤ Nat.card {c // T c a}) :
    Nat.card {p : β × α // S p.1 p.2} ≤ Nat.card {p : γ × α // T p.1 p.2} := by
  have h1 := h5_fib α β γ (fun a b => S b a) (fun a c => T c a) h
  have e1 : Nat.card {p : β × α // S p.1 p.2} = Nat.card {p : α × β // S p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm β α).subtypeEquiv (fun p => Iff.rfl))
  have e2 : Nat.card {p : γ × α // T p.1 p.2} = Nat.card {p : α × γ // T p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm γ α).subtypeEquiv (fun p => Iff.rfl))
  rw [e1, e2]
  exact h1

def h5_G (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y0 e : Fin n → ZMod 2) (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : ↥K) : Prop :=
  ∀ i, mark i = true →
    h5_P n hn i (Y0 + mix n hn (k : Fin n → ZMod 2)) = (N (k : Fin n → ZMod 2) + e) i

def h5_T1 (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y0 : Fin n → ZMod 2) (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ↥K)
    (κ : ↥(h5_KZ n hn K)) : Prop :=
  ∀ i, mark i = true →
    h5_g n hn i (Y0 + mix n hn (k : Fin n → ZMod 2)) (mix n hn (κ : Fin n → ZMod 2)) =
      N (κ : Fin n → ZMod 2) i

def h5_T0 (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (k : ↥K) (κ : ↥(h5_KZ n hn K)) : Prop :=
  ∀ i, mark i = true →
    h5_g n hn i (mix n hn (k : Fin n → ZMod 2)) (mix n hn (κ : Fin n → ZMod 2)) = 0

lemma h5_step1_key (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k g0 g : ↥K)
    (hg0 : h5_G n hn mark K Y0 e N g0)
    (hm0 : (g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K)
    (hg : h5_G n hn mark K Y0 e N g)
    (hd : (g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2) ∈ h5_KZ n hn K) :
    h5_T1 n hn mark K Y0 N k ⟨(g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2), hd⟩ := by
  intro i hi
  have o1 : even n (mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2))) = 0 :=
    ((h5_mem_KZ n hn K _).1 hd).2
  have o2 : even n (mix n hn ((g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2))) = 0 :=
    ((h5_mem_KZ n hn K _).1 hm0).2
  have e1 : Y0 + mix n hn (g : Fin n → ZMod 2) = (Y0 + mix n hn (g0 : Fin n → ZMod 2)) +
      mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2)) := by
    rw [mix_sub]
    abel
  have e2 : Y0 + mix n hn (g0 : Fin n → ZMod 2) = (Y0 + mix n hn (k : Fin n → ZMod 2)) +
      mix n hn ((g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2)) := by
    rw [mix_sub]
    abel
  have h1 := hg i hi
  rw [e1, h5_P_add n hn h2 i _ _ o1, hg0 i hi, e2, h5_g_add,
    h5_g_odd n hn h2 i _ _ o2 o1, add_zero] at h1
  show h5_g n hn i (Y0 + mix n hn (k : Fin n → ZMod 2))
    (mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2))) =
    N ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2)) i
  rw [map_sub, Pi.sub_apply]
  simp only [Pi.add_apply] at h1
  linear_combination h1

lemma h5_step1_fib (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ↥K) :
    Nat.card {g : ↥K // h5_G n hn mark K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K} ≤
    Nat.card {κ : ↥(h5_KZ n hn K) // h5_T1 n hn mark K Y0 N k κ} := by
  rcases isEmpty_or_nonempty {g : ↥K // h5_G n hn mark K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K} with hE | ⟨⟨g0, hg0, hm0⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · have hd : ∀ g : {g : ↥K // h5_G n hn mark K Y0 e N g ∧
        (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K},
        (g.1 : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2) ∈ h5_KZ n hn K := by
      intro g
      have h := (h5_KZ n hn K).sub_mem g.2.2 hm0
      rw [sub_sub_sub_cancel_right] at h
      exact h
    refine Nat.card_le_card_of_injective (fun g =>
      ⟨⟨(g.1 : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2), hd g⟩,
        h5_step1_key n hn h2 mark K Y0 e N k g0 g.1 hg0 hm0 g.2.1 (hd g)⟩) ?_
    intro g g' hgg
    simp only [Subtype.mk.injEq, sub_left_inj] at hgg
    exact Subtype.ext (Subtype.ext hgg)

lemma h5_step2_fib (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (κ : ↥(h5_KZ n hn K)) :
    Nat.card {k : ↥K // h5_T1 n hn mark K Y0 N k κ} ≤
    Nat.card {k : ↥K // h5_T0 n hn mark K k κ} := by
  rcases isEmpty_or_nonempty {k : ↥K // h5_T1 n hn mark K Y0 N k κ} with hE | ⟨⟨k0, hk0⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · refine Nat.card_le_card_of_injective (fun k => ⟨k.1 - k0, ?_⟩) ?_
    · intro i hi
      have e1 : Y0 + mix n hn (k.1 : Fin n → ZMod 2) = (Y0 + mix n hn (k0 : Fin n → ZMod 2)) +
          mix n hn ((k.1 - k0 : ↥K) : Fin n → ZMod 2) := by
        rw [Submodule.coe_sub, mix_sub]
        abel
      have h1 := k.2 i hi
      rw [e1, h5_g_add, hk0 i hi] at h1
      exact add_left_cancel (h1.trans (add_zero _).symm)
    · intro k k' hkk
      exact Subtype.ext (sub_left_inj.mp (congrArg Subtype.val hkk))

lemma h5_step1 (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (h5_KZ n hn K) * Nat.card {k : ↥K // h5_G n hn mark K Y0 e N k} ≤
    Nat.card {p : ↥K × ↥(h5_KZ n hn K) // h5_T1 n hn mark K Y0 N p.1 p.2} := by
  have h1 : Nat.card (↥(h5_KZ n hn K) × {k : ↥K // h5_G n hn mark K Y0 e N k}) ≤
      Nat.card {p : ↥K × ↥K // h5_G n hn mark K Y0 e N p.2 ∧
        (p.2 : Fin n → ZMod 2) - (p.1 : Fin n → ZMod 2) ∈ h5_KZ n hn K} := by
    refine Nat.card_le_card_of_injective (fun q =>
      ⟨(⟨(q.2.1 : Fin n → ZMod 2) - (q.1 : Fin n → ZMod 2),
        K.sub_mem q.2.1.2 ((h5_mem_KZ n hn K _).1 q.1.2).1⟩, q.2.1), ⟨q.2.2, ?_⟩⟩) ?_
    · show (q.2.1 : Fin n → ZMod 2) - ((q.2.1 : Fin n → ZMod 2) - (q.1 : Fin n → ZMod 2)) ∈
        h5_KZ n hn K
      rw [sub_sub_cancel]
      exact q.1.2
    · intro q q' hqq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at hqq
      have h3 : q.2 = q'.2 := Subtype.ext hqq.2
      have h4 := hqq.1
      rw [hqq.2] at h4
      exact Prod.ext (Subtype.ext (sub_right_injective h4)) h3
  rw [Nat.card_prod] at h1
  exact le_trans h1 (h5_fib ↥K ↥K ↥(h5_KZ n hn K)
    (fun k g => h5_G n hn mark K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K)
    (fun k κ => h5_T1 n hn mark K Y0 N k κ)
    (fun k => h5_step1_fib n hn h2 mark K Y0 e N k))

lemma h5_step3 (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {p : ↥K × ↥(h5_KZ n hn K) // h5_T0 n hn mark K p.1 p.2} =
    Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun u => ?_))
  constructor
  · intro h i hi
    rw [h5_tau_apply]
    exact (h5_P_even n hn h2 i _ _ (h5_odd_KZ n hn K u.2)).trans (h i hi)
  · intro h i hi
    have h1 := h i hi
    rw [h5_tau_apply] at h1
    exact (h5_P_even n hn h2 i _ _ (h5_odd_KZ n hn K u.2)).symm.trans h1

lemma h5_pairs (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (h5_KZ n hn K) * Nat.card {k : ↥K // h5_G n hn mark K Y0 e N k} ≤
    Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} := by
  rw [← h5_step3 n hn h2 mark K]
  exact le_trans (h5_step1 n hn h2 mark K Y0 e N)
    (h5_fib2 ↥(h5_KZ n hn K) ↥K ↥K (fun k κ => h5_T1 n hn mark K Y0 N k κ)
      (fun k κ => h5_T0 n hn mark K k κ) (fun κ => h5_step2_fib n hn mark K Y0 N κ))

lemma h5_move : ∀ X s t : ZMod 2, X + s = t ↔ X = s + t := by
  decide

lemma h5_good (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (name c : Fin n → ZMod 2)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (w0 : Fin n → ZMod 2)
    (A L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b c0 : Fin n → ZMod 2)
    (hL : ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i =
        mix n hn w (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2)) + (L w + c0) i) :
    Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} =
    Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun k =>
    forall_congr' (fun i => imp_congr_right (fun _ => ?_))))
  have e : (L (w0 + (k : Fin n → ZMod 2)) + c0) i + (A (w0 + (k : Fin n → ZMod 2)) + b) i =
      ((L + A) (k : Fin n → ZMod 2) + (L w0 + c0 + A w0 + b)) i := by
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    ring
  rw [hL, mix_add, h5_move, e]
  exact Iff.rfl

lemma cell_count (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (w0 : Fin n → ZMod 2) (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : Fin n → ZMod 2) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Nat.card D * Nat.card K ≤ 2^n * 16 ∧
      (2:ℤ)^n * (Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} : ℤ) ≤
      (Nat.card K : ℤ) * Ssum n hn mark D := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  have h2 : 2 ∣ n := Dvd.dvd.trans (by norm_num) h6
  refine ⟨orth n (h5_tau n hn K), h5_base_mem n hn h6 K, h5_even_mem n hn K,
    h5_card_D n hn h6 K, ?_⟩
  have hp := h5_pairs n hn h2 mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A)
  have hf := fourier_count n hn mark (h5_tau n hn K)
  rw [Nat.card_prod] at hf
  rw [h5_good n hn mark name c K w0 A L b c0 hL]
  have hpos : (0:ℤ) < (Nat.card (h5_KZ n hn K) : ℤ) := Nat.cast_pos.mpr Nat.card_pos
  have hp' : (Nat.card (h5_KZ n hn K) : ℤ) *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)
      ≤ (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) := by
    exact_mod_cast hp
  have h3 : (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
      ≤ (Nat.card (h5_KZ n hn K) : ℤ) *
        ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
    calc (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
        = (2:ℤ)^n * ((Nat.card (h5_KZ n hn K) : ℤ) * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)) := by ring
      _ ≤ (2:ℤ)^n *
          (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = ((Nat.card K * Nat.card (h5_KZ n hn K) : ℕ) : ℤ) *
          Ssum n hn mark (orth n (h5_tau n hn K)) := hf
      _ = (Nat.card (h5_KZ n hn K) : ℤ) *
          ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
        push_cast
        ring
  exact le_of_mul_le_mul_left h3 hpos

lemma h6_cell (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2))
    (w0 : Fin n → ZMod 2) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ h+4 ∧
      (2:ℤ)^n * (Nat.card {w : Fin n → ZMod 2 // (∀ i, mark i = true →
        out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i) ∧
          run n h ask w = run n h ask w0} : ℤ) ≤
      (Nat.card {w : Fin n → ZMod 2 // run n h ask w = run n h ask w0} : ℤ) *
        Ssum n hn mark D := by
  obtain ⟨K, hK, hKc⟩ := cell_structure n h ask w0
  obtain ⟨D, hb, he, hDK, hcount⟩ :=
    cell_count n hn h6 mark name c K w0 (A (run n h ask w0)) (b (run n h ask w0))
  refine ⟨D, hb, he, ?_, ?_⟩
  · have h1 : Nat.card D * 2^n ≤ 2^(h+4) * 2^n := by
      calc Nat.card D * 2^n ≤ Nat.card D * (Nat.card K * 2^h) := Nat.mul_le_mul_left _ hKc
        _ = Nat.card D * Nat.card K * 2^h := by ring
        _ ≤ 2^n * 16 * 2^h := Nat.mul_le_mul_right _ hDK
        _ = 2^(h+4) * 2^n := by ring
    have h2 : Nat.card D ≤ 2^(h+4) := Nat.le_of_mul_le_mul_right h1 (by positivity)
    have h3 : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
      simp
    rw [h3] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  · have hrun : ∀ k : K, run n h ask (w0 + (k : Fin n → ZMod 2)) = run n h ask w0 := by
      intro k
      rw [hK, add_sub_cancel_left]
      exact k.2
    have e2 : Nat.card K = Nat.card {w : Fin n → ZMod 2 // run n h ask w = run n h ask w0} :=
      Nat.card_congr
        { toFun := fun k => ⟨w0 + (k : Fin n → ZMod 2), hrun k⟩
          invFun := fun w => ⟨w.1 - w0, (hK _).mp w.2⟩
          left_inv := fun k => Subtype.ext (add_sub_cancel_left _ _)
          right_inv := fun w => Subtype.ext (add_sub_cancel _ _) }
    have e1 : Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (run n h ask w0) (w0 + (k : Fin n → ZMod 2)) + b (run n h ask w0)) i} =
        Nat.card {w : Fin n → ZMod 2 // (∀ i, mark i = true →
          out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i) ∧
            run n h ask w = run n h ask w0} :=
      Nat.card_congr
        { toFun := fun k => ⟨w0 + (k.1 : Fin n → ZMod 2), by
            refine ⟨?_, hrun k.1⟩
            rw [hrun k.1]
            exact k.2⟩
          invFun := fun w => ⟨⟨w.1 - w0, (hK _).mp w.2.2⟩, by
            have hw := w.2.1
            rw [w.2.2] at hw
            have hc : w0 + (w.1 - w0) = w.1 := add_sub_cancel _ _
            show ∀ i, mark i = true → out n hn name c (w0 + (w.1 - w0)) i =
              (A (run n h ask w0) (w0 + (w.1 - w0)) + b (run n h ask w0)) i
            rw [hc]
            exact hw⟩
          left_inv := fun k => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _))
          right_inv := fun w => Subtype.ext (add_sub_cancel _ _) }
    rw [← e1, ← e2]
    exact hcount

lemma h6_card_filter {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Nat.card {a : α // P a} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma h6_fiber_sum {α : Type} [Fintype α] [Nonempty α] (f : α → ℕ) (P : α → Prop)
    (hcell : ∀ a0, (Nat.card α : ℤ) * (Nat.card {a : α // P a ∧ f a = f a0} : ℤ) ≤
      (Nat.card {a : α // f a = f a0} : ℤ) * ((Nat.card {a : α // P a} : ℤ) - 1)) : False := by
  classical
  have hG : Nat.card {a : α // P a} =
      ∑ p ∈ Finset.univ.image f, Nat.card {a : α // P a ∧ f a = p} := by
    rw [h6_card_filter, Finset.card_eq_sum_card_fiberwise
      (f := f) (t := Finset.univ.image f) (fun a _ => Finset.mem_coe.mpr
        (Finset.mem_image_of_mem f (Finset.mem_univ a)))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h6_card_filter, Finset.filter_filter]
  have hC : Nat.card α = ∑ p ∈ Finset.univ.image f, Nat.card {a : α // f a = p} := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := f) (t := Finset.univ.image f) (fun a _ => Finset.mem_coe.mpr
        (Finset.mem_image_of_mem f (Finset.mem_univ a)))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h6_card_filter]
  have hsum : ∑ p ∈ Finset.univ.image f,
      (Nat.card α : ℤ) * (Nat.card {a : α // P a ∧ f a = p} : ℤ) ≤
      ∑ p ∈ Finset.univ.image f,
        (Nat.card {a : α // f a = p} : ℤ) * ((Nat.card {a : α // P a} : ℤ) - 1) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hp
    exact hcell a0
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hG' : (Nat.card {a : α // P a} : ℤ) =
      ∑ p ∈ Finset.univ.image f, (Nat.card {a : α // P a ∧ f a = p} : ℤ) := by
    exact_mod_cast hG
  have hC' : (Nat.card α : ℤ) =
      ∑ p ∈ Finset.univ.image f, (Nat.card {a : α // f a = p} : ℤ) := by
    exact_mod_cast hC
  rw [← hG', ← hC'] at hsum
  have hpos : (0:ℤ) < (Nat.card α : ℤ) := by
    exact_mod_cast Nat.card_pos
  nlinarith

lemma upper (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ h+4 ∧
      (Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true →
        out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i} : ℤ) ≤
      Ssum n hn mark D := by
  by_contra hcon
  have hW : ((2:ℤ)^n) = (Nat.card (Fin n → ZMod 2) : ℤ) := by
    simp [Nat.card_eq_fintype_card]
  refine h6_fiber_sum (run n h ask) (fun w => ∀ i, mark i = true →
    out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i) (fun w0 => ?_)
  obtain ⟨D, hb, he, hf, hc⟩ := h6_cell n hn h6 h mark name c ask A b w0
  have hlt := lt_of_not_ge (fun hle => hcon ⟨D, hb, he, hf, hle⟩)
  rw [← hW]
  refine le_trans hc (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  linarith

lemma h4_z2_pred : ∀ x y s t l c : ZMod 2,
    (x * y + (l + c) = t * x + s * y + l + (s * t + c) ↔ (x - s) * (y - t) = 0) := by
  decide

lemma h4_out_pred (n : ℕ) (hn : 0 < n) (name c wp : Fin n → ZMod 2) :
    ∃ (A' : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b' : Fin n → ZMod 2),
      ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i = (A' w + b') i ↔
        mix n hn (w - wp) (ix n hn (i.val+1)) * mix n hn (w - wp) (ix n hn (i.val+2)) = 0 := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  refine ⟨LinearMap.pi (fun i =>
      ((mix n hn wp (ix n hn (i.val+2))) • ((LinearMap.proj (ix n hn (i.val+1))) ∘ₗ mixL n hn) +
      (mix n hn wp (ix n hn (i.val+1))) • ((LinearMap.proj (ix n hn (i.val+2))) ∘ₗ mixL n hn) +
      (LinearMap.proj i) ∘ₗ L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)),
    fun i => mix n hn wp (ix n hn (i.val+1)) * mix n hn wp (ix n hn (i.val+2)) + c0 i, ?_⟩
  intro w i
  rw [hL w i, mix_sub]
  simp only [Pi.add_apply, Pi.sub_apply, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, mixL_apply, smul_eq_mul]
  exact h4_z2_pred _ _ _ _ _ _

lemma h4_count (n : ℕ) (N : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (P : (Fin n → ZMod 2) → Prop)
    (hr1 : ∀ w, w - r w ∈ N) (hr2 : ∀ w, ∀ u ∈ N, r (r w + u) = r w) :
    Nat.card N * Nat.card {w : Fin n → ZMod 2 // P (w - r w)} =
      2^n * Nat.card {u : N // P (u : Fin n → ZMod 2)} := by
  have hΦ : Function.Involutive (fun x : (Fin n → ZMod 2) × N =>
      ((r x.1 + (x.2 : Fin n → ZMod 2), ⟨x.1 - r x.1, hr1 x.1⟩) : (Fin n → ZMod 2) × N)) := by
    rintro ⟨w, u⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show r (r w + (u : Fin n → ZMod 2)) + (w - r w) = w
      rw [hr2 w u u.2, add_sub_cancel]
    · show r w + (u : Fin n → ZMod 2) - r (r w + (u : Fin n → ZMod 2)) = u
      rw [hr2 w u u.2, add_sub_cancel_left]
  have e1 : {x : (Fin n → ZMod 2) × N // P (x.1 - r x.1)} ≃
      {x : (Fin n → ZMod 2) × N // P (x.2 : Fin n → ZMod 2)} :=
    Equiv.subtypeEquiv (Function.Involutive.toPerm _ hΦ) (fun x => Iff.rfl)
  have e2 : {x : (Fin n → ZMod 2) × N // P (x.1 - r x.1)} ≃
      {w : Fin n → ZMod 2 // P (w - r w)} × N :=
    Equiv.prodSubtypeFstEquivSubtypeProd (p := fun w => P (w - r w))
  have e3 : {x : (Fin n → ZMod 2) × N // P (x.2 : Fin n → ZMod 2)} ≃
      (Fin n → ZMod 2) × {u : N // P (u : Fin n → ZMod 2)} :=
    { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
      invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Nat.card_congr (e2.symm.trans (e1.trans e3))
  rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h1
  rw [mul_comm, h1]

lemma h4_nonadaptive_aux (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (name c : Fin n → ZMod 2)
    (N : Submodule (ZMod 2) (Fin n → ZMod 2)) (R : (Fin n → ZMod 2) → ℕ)
    (hR : ∀ w w', R w = R w' ↔ w - w' ∈ N) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card N * Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true →
        out n hn name c w i = (A (R w) w + b (R w)) i} =
      2^n * Nat.card {u : N // adm n hn mark (mix n hn (u : Fin n → ZMod 2))} := by
  have hrep : ∀ w, R (Function.invFun R (R w)) = R w := fun w => Function.invFun_eq ⟨w, rfl⟩
  choose A b hAb using fun p : ℕ => h4_out_pred n hn name c (Function.invFun R p)
  refine ⟨A, b, ?_⟩
  have hgood : ∀ w, (∀ i, mark i = true → out n hn name c w i = (A (R w) w + b (R w)) i) ↔
      adm n hn mark (mix n hn (w - Function.invFun R (R w))) := by
    intro w
    unfold adm
    exact forall_congr' (fun i => imp_congr_right (fun _ => hAb _ w i))
  rw [Nat.card_congr (Equiv.subtypeEquivRight hgood)]
  refine h4_count n N (fun w => Function.invFun R (R w)) (fun x => adm n hn mark (mix n hn x))
    (fun w => (hR w _).mp (hrep w).symm) (fun w u hu => ?_)
  refine congrArg (Function.invFun R) (((hR _ _).mpr ?_).trans (hrep w))
  rw [add_sub_cancel_left]
  exact hu

lemma nonadaptive_count (n : ℕ) (hn : 0 < n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (φ : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card (LinearMap.ker (LinearMap.pi φ)) *
        Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true → out n hn name c w i =
          (A (run n h (fun j _ => φ j) w) w + b (run n h (fun j _ => φ j) w)) i} =
      2^n * Nat.card {u : LinearMap.ker (LinearMap.pi φ) //
        adm n hn mark (mix n hn (u : Fin n → ZMod 2))} := by
  refine h4_nonadaptive_aux n hn mark name c _ _ ?_
  intro w w'
  obtain ⟨p, hp⟩ := run_eq_iff n h (fun j _ => φ j) w'
  rw [hp w, LinearMap.mem_ker]
  constructor
  · intro hj
    funext j
    exact hj j
  · intro hj j
    exact congrFun hj j

lemma h6_orth_eq (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (hbase : ∀ j, base n j ∈ D)
    (v : Fin h → (Fin n → ZMod 2)) (hvD : ∀ j, v j ∈ D)
    (hspan : D ≤ Submodule.span (ZMod 2) (Set.range (base n)) ⊔
      Submodule.span (ZMod 2) (Set.range v))
    (φ : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hφ : ∀ j w, φ j w = dot n (v j) (mix n hn w)) :
    orth n ((mixL n hn).comp (LinearMap.ker (LinearMap.pi φ)).subtype) = D := by
  apply le_antisymm
  · intro z hz
    rw [mem_orth] at hz
    apply double_orth n D z
    intro x hx
    have hxb : ∀ j, dot n (base n j) x = 0 := by
      intro j
      rw [dot_comm]
      exact hx _ (hbase j)
    obtain ⟨w, rfl⟩ := mix_surj n hn h6 x hxb
    have hwN : w ∈ LinearMap.ker (LinearMap.pi φ) := by
      rw [LinearMap.mem_ker]
      funext j
      show φ j w = 0
      rw [hφ, dot_comm]
      exact hx _ (hvD j)
    have hzw := hz ⟨w, hwN⟩
    rw [dot_comm]
    exact hzw
  · refine le_trans hspan (sup_le ?_ ?_)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_orth]
      intro u
      exact base_dot_mix n hn h6 j _
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_orth]
      intro u
      have hu := u.2
      rw [LinearMap.mem_ker] at hu
      have huj : φ j u.1 = 0 := congrFun hu j
      rw [hφ] at huj
      exact huj

lemma lower (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hbase : ∀ j, base n j ∈ D) (heven : ∀ z ∈ D, even n z ∈ D)
    (hfin : Module.finrank (ZMod 2) D ≤ h+4) :
    ∃ (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      (∃ v : Fin h → (Fin n → ZMod 2),
        (∀ j, even n (v j) = v j ∨ even n (v j) = 0) ∧
        (∀ j p w, ask j p w = ∑ i, v j i * mix n hn w i)) ∧
      Ssum n hn mark D ≤ (Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true →
        out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i} : ℤ) := by
  have hBD : Submodule.span (ZMod 2) (Set.range (base n)) ≤ D := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hbase j
  have hBe : ∀ z ∈ Submodule.span (ZMod 2) (Set.range (base n)),
      even n z ∈ Submodule.span (ZMod 2) (Set.range (base n)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases even_base n j with h1 | h1
      · rw [h1]
        exact Submodule.subset_span ⟨j, rfl⟩
      · rw [h1]
        exact Submodule.zero_mem _
    | zero =>
      rw [even_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [even_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [even_smul]
      exact Submodule.smul_mem _ a hx
  have hfin' : Module.finrank (ZMod 2) D ≤
      h + Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (base n))) := by
    have h4 := base_span_finrank n hn h6
    omega
  obtain ⟨v, hv1, hv2, hv3⟩ := lane_pure_span n h _ D hBD hBe heven hfin'
  have hφ : ∀ j w, ((dotL n (v j)).comp (mixL n hn)) w = dot n (v j) (mix n hn w) := by
    intro j w
    show dot n (mix n hn w) (v j) = dot n (v j) (mix n hn w)
    exact dot_comm n _ _
  obtain ⟨A, b, hAb⟩ :=
    nonadaptive_count n hn h mark name c (fun j => (dotL n (v j)).comp (mixL n hn))
  refine ⟨fun j _ => (dotL n (v j)).comp (mixL n hn), A, b, ⟨v, hv1, ?_⟩, ?_⟩
  · intro j p w
    exact hφ j w
  · have hF := fourier_count n hn mark ((mixL n hn).comp (LinearMap.ker (LinearMap.pi
      (fun j => (dotL n (v j)).comp (mixL n hn)))).subtype)
    rw [h6_orth_eq n hn h6 h D hbase v hv2 hv3 _ hφ] at hF
    have hAbZ := congrArg (fun k : ℕ => (k : ℤ)) hAb
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hAbZ
    have hEq := hAbZ.trans hF
    have hNpos : (0:ℤ) < (Nat.card (LinearMap.ker (LinearMap.pi
        (fun j => (dotL n (v j)).comp (mixL n hn)))) : ℤ) := by
      exact_mod_cast Nat.card_pos
    exact le_of_eq (mul_left_cancel₀ hNpos.ne' hEq).symm

lemma final (t : ℕ) (ht : 0 < t) (h : ℕ) (mark : Fin (6*t) → Bool)
    (name c : Fin (6*t) → ZMod 2) (k : ℕ) (fixed : Bool) :
    (∃ (ask : Fin h → ℕ → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (A : ℕ → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] (Fin (6*t) → ZMod 2))
        (b : ℕ → (Fin (6*t) → ZMod 2)),
      (fixed = true → ∃ v : Fin h → (Fin (6*t) → ZMod 2),
        (∀ j, even (6*t) (v j) = v j ∨ even (6*t) (v j) = 0) ∧
        (∀ j p w, ask j p w =
          ∑ i, v j i * mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w i)) ∧
      k ≤ Nat.card {w : Fin (6*t) → ZMod 2 // ∀ i, mark i = true →
        out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w i =
          (A (run (6*t) h ask w) w + b (run (6*t) h ask w)) i}) ↔
    ∃ D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2),
      (∀ j, base (6*t) j ∈ D) ∧ (∀ z ∈ D, even (6*t) z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ h+4 ∧
      (k : ℤ) ≤ Ssum (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) mark D := by
  have h6 : 6 ∣ 6*t := Dvd.intro t rfl
  constructor
  · rintro ⟨ask, A, b, -, hk⟩
    obtain ⟨D, h1, h2, h3, h4⟩ :=
      upper (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 h mark name c ask A b
    exact ⟨D, h1, h2, h3, le_trans (Nat.cast_le.mpr hk) h4⟩
  · rintro ⟨D, h1, h2, h3, h4⟩
    obtain ⟨ask, A, b, hv, hc⟩ :=
      lower (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 h mark name c D h1 h2 h3
    exact ⟨ask, A, b, fun _ => hv, Nat.cast_le.mp (le_trans h4 hc)⟩

lemma gl_cell_count (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (w0 : Fin n → ZMod 2) (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : Fin n → ZMod 2) :
      (2:ℤ)^n * (Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} : ℤ) ≤
      (Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K)) := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  have h2 : 2 ∣ n := Dvd.dvd.trans (by norm_num) h6
  have hp := h5_pairs n hn h2 mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A)
  have hf := fourier_count n hn mark (h5_tau n hn K)
  rw [Nat.card_prod] at hf
  rw [h5_good n hn mark name c K w0 A L b c0 hL]
  have hpos : (0:ℤ) < (Nat.card (h5_KZ n hn K) : ℤ) := Nat.cast_pos.mpr Nat.card_pos
  have hp' : (Nat.card (h5_KZ n hn K) : ℤ) *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)
      ≤ (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) := by
    exact_mod_cast hp
  have h3 : (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
      ≤ (Nat.card (h5_KZ n hn K) : ℤ) *
        ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
    calc (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
        = (2:ℤ)^n * ((Nat.card (h5_KZ n hn K) : ℤ) * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)) := by ring
      _ ≤ (2:ℤ)^n *
          (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = ((Nat.card K * Nat.card (h5_KZ n hn K) : ℕ) : ℤ) *
          Ssum n hn mark (orth n (h5_tau n hn K)) := hf
      _ = (Nat.card (h5_KZ n hn K) : ℤ) *
          ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
        push_cast
        ring
  exact le_of_mul_le_mul_left h3 hpos

def markT (n : ℕ) : Fin n → Bool := fun _ => true

def es (n s : ℕ) : Fin n → ZMod 2 := fun i => if i.val = s then 1 else 0

noncomputable def Bsp (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (base n))

noncomputable def D0 (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Bsp n ⊔ Submodule.span (ZMod 2) {es n 0}

abbrev C4 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

noncomputable def bc (n : ℕ) (c : C4) : Fin n → ZMod 2 :=
  c.1 • base n 0 + c.2.1 • base n 1 + c.2.2.1 • base n 2 + c.2.2.2 • base n 3

lemma bc_mem (n : ℕ) (c : C4) : bc n c ∈ Bsp n := by
  unfold bc Bsp
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

lemma st_mem_Bsp (n : ℕ) (z : Fin n → ZMod 2) :
    z ∈ Bsp n ↔ ∃ c : C4, z = bc n c := by
  unfold Bsp
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(g 0, g 1, g 2, g 3), ?_⟩
    rw [← hg, Fin.sum_univ_four]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨![c.1, c.2.1, c.2.2.1, c.2.2.2], ?_⟩
    rw [Fin.sum_univ_four]
    rfl

lemma st_Ssum_image {α : Type} [Fintype α] (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (f : α → (Fin n → ZMod 2))
    (hf : Function.Injective f) (hD : ∀ z, z ∈ D ↔ ∃ a, z = f a) :
    Ssum n hn mark D = ∑ a, tw n hn mark (f a) := by
  classical
  rw [Ssum_eq, ← Finset.sum_filter]
  have e : (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D) =
      Finset.univ.image f := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hD]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  rw [e]
  exact Finset.sum_image (fun a _ b _ h => hf h)

def fm_M (a : ZMod 2) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (if a = 0 then 1 else -1); 1, 0]

def fm_beta (c : C4) (r : ℕ) : ZMod 2 :=
  c.1 * h3_b 0 r + c.2.1 * h3_b 1 r + c.2.2.1 * h3_b 2 r + c.2.2.2 * h3_b 3 r

lemma fm_tw (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw n hn (markT n) z = (List.ofFn (fun i : Fin n => fm_M (z i))).prod.trace := by
  unfold tw markT fm_M
  simp only [ite_true]
  congr 3
  all_goals first
    | (funext b; exact Subsingleton.elim _ _)
    | (funext i; split_ifs <;> rfl)

lemma fm_ofFn (n : ℕ) (g : ℕ → Matrix (Fin 2) (Fin 2) ℤ) :
    List.ofFn (fun i : Fin n => g i.val) = (List.range n).map g := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

lemma fm_base (t : ℕ) (ht : 0 < 6 * t) (j : Fin 4) (i : Fin (6 * t)) :
    base (6 * t) j i = h3_b j (i.val % 6) := by
  have h := h3_base_ix (6 * t) ht (Dvd.intro t rfl) j i.val
  rw [ix_self] at h
  rw [h, h3_b_mod]

lemma fm_bc (t : ℕ) (ht : 0 < 6 * t) (c : C4) (i : Fin (6 * t)) :
    bc (6 * t) c i = fm_beta c (i.val % 6) := by
  simp only [bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fm_base t ht, fm_beta]


abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def step (s : ℤ) : Mat := !![1+s,1;1,1]

def pathProd (s : ℕ → ℤ) : ℕ → Mat
  | 0 => 1
  | m + 1 => pathProd s m * step (s m)

def total (A : Mat) : ℤ := A 0 0 + A 0 1 + A 1 0 + A 1 1

def phase (d i : ℕ) : ℤ := if (d+i)%3 = 0 then 1 else -1

def signedPaths (m : ℕ) : ℤ :=
  ∑ d : Fin 3, total (pathProd (phase d.val) m)

def lo (r : ℕ) : ℤ := if r = 0 then 6 else if r = 1 then 11 else 19

def hi (r : ℕ) : ℤ := if r = 0 then 34 else if r = 1 then 63 else 111

def companion : Mat := !![0,1;-1,6]

lemma pathProd_add (s : ℕ → ℤ) (a b : ℕ) :
    pathProd s (a+b) = pathProd s a * pathProd (fun i => s (a+i)) b := by
  induction b with
  | zero => simp [pathProd]
  | succ b ih => rw [Nat.add_succ, pathProd, ih, pathProd, mul_assoc]

lemma pathProd_const (s : ℤ) (m : ℕ) : pathProd (fun _ => s) m = step s ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pathProd, ih, pow_succ]

lemma phase_stride (d : ℕ) : (fun i => phase d (3+i)) = phase d := by
  funext i
  unfold phase
  rw [show (d+(3+i))%3 = (d+i)%3 by omega]

lemma pathProd_blocks (d q r : ℕ) :
    pathProd (phase d) (3*q+r) = pathProd (phase d) 3 ^ q * pathProd (phase d) r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 3*(q+1)+r = 3+(3*q+r) by omega, pathProd_add, phase_stride, ih, pow_succ', mul_assoc]

lemma phase_ch (d : Fin 3) :
    (pathProd (phase d.val) 3)^2 = (6 : ℤ) • pathProd (phase d.val) 3 - 1 := by
  fin_cases d <;> decide

lemma phase_rec (d : Fin 3) (q r : ℕ) :
    total (pathProd (phase d) (3*(q+2)+r)) =
      6 * total (pathProd (phase d) (3*(q+1)+r)) - total (pathProd (phase d) (3*q+r)) := by
  rw [pathProd_blocks, pathProd_blocks, pathProd_blocks, pow_add, phase_ch, mul_sub,
    mul_smul_comm, mul_one, sub_mul, smul_mul_assoc, ← pow_succ]
  simp only [total, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma signedPaths_rec (q r : ℕ) :
    signedPaths (3*(q+2)+r) = 6*signedPaths (3*(q+1)+r) - signedPaths (3*q+r) := by
  simp only [signedPaths, phase_rec, Finset.sum_sub_distrib, Finset.mul_sum]

lemma unsigned_vec (m : ℕ) :
    (step 1 ^ m).mulVec ![1,1] = ![(Nat.fib (2*m+2) : ℤ), (Nat.fib (2*m+1) : ℤ)] := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    have a := @Nat.fib_add_two (2*m+1)
    have b := @Nat.fib_add_two (2*m+2)
    have a' : (Nat.fib (2*m+3) : ℤ) = Nat.fib (2*m+1) + Nat.fib (2*m+2) := by exact_mod_cast a
    have b' : (Nat.fib (2*m+4) : ℤ) = Nat.fib (2*m+2) + Nat.fib (2*m+3) := by exact_mod_cast b
    rw [show 2*(m+1)+2 = 2*m+4 by omega, show 2*(m+1)+1 = 2*m+3 by omega, b', a']
    ext i
    fin_cases i <;> simp [step, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma unsigned_paths (m : ℕ) :
    total (pathProd (fun _ => 1) m) = (Nat.fib (2*m+3) : ℤ) := by
  rw [pathProd_const]
  have a := congrFun (unsigned_vec m) 0
  have b := congrFun (unsigned_vec m) 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a b
  have e : (Nat.fib (2*m+3) : ℤ) = Nat.fib (2*m+1) + Nat.fib (2*m+2) := by
    exact_mod_cast @Nat.fib_add_two (2*m+1)
  unfold total
  linarith

lemma signedPaths_vec (r : Fin 3) (q : ℕ) :
    (companion^q).mulVec ![lo r.val,hi r.val] =
      ![signedPaths (3*q+r.val), signedPaths (3*(q+1)+r.val)] := by
  induction q with
  | zero => fin_cases r <;> decide
  | succ q ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    ext i
    fin_cases i <;> simp [companion, Matrix.mulVec, dotProduct, Fin.sum_univ_two, signedPaths_rec]
    ring

lemma signed_paths (m : ℕ) :
    signedPaths m =
      (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^(m/3)).mulVec
        ![if m%3 = 0 then 6 else if m%3 = 1 then 11 else 19,
          if m%3 = 0 then 34 else if m%3 = 1 then 63 else 111]) 0 := by
  have e := congrFun (signedPaths_vec ⟨m%3, Nat.mod_lt _ (by decide)⟩ (m/3)) 0
  change _ = signedPaths (3*(m/3)+m%3) at e
  rw [Nat.div_add_mod] at e
  exact e.symm

lemma path_price (h m : ℕ) :
    (2 : ℤ)^(2*h-1) * (total (pathProd (fun _ => 1) m) + signedPaths m) =
      2^(2*h-1)*((Nat.fib (2*m+3) : ℤ) +
        (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^(m/3)).mulVec
          ![if m%3 = 0 then 6 else if m%3 = 1 then 11 else 19,
            if m%3 = 0 then 34 else if m%3 = 1 then 63 else 111]) 0) := by
  rw [unsigned_paths, signed_paths]

noncomputable def wt (n : ℕ) (z : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => z i ≠ 0)).card

noncomputable def Iset (n : ℕ) (hn : 0 < n) : Finset (Fin n → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun x => adm n hn (markT n) x)

def blocked (n : ℕ) (hn : 0 < n) (s : Fin n) (x : Fin n → ZMod 2) : Prop :=
  x (ix n hn (s.val + n - 1)) = 1 ∨ x (ix n hn (s.val + 1)) = 1

noncomputable def cntB (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ((Iset n hn).filter (fun x => ∀ s ∈ S, blocked n hn s x)).card
noncomputable def kc_B (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Iset n hn).filter (fun x => ∀ s ∈ S, blocked n hn s x)

lemma kc_cntB (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : cntB n hn S = (kc_B n hn S).card := rfl

lemma kc_mem_B (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    x ∈ kc_B n hn S ↔ x ∈ Iset n hn ∧ ∀ s ∈ S, blocked n hn s x := by
  unfold kc_B
  simp only [Finset.mem_filter]

lemma kc_LR (n : ℕ) (hn : 0 < n) (s : Fin n) :
    ix n hn ((ix n hn (s.val + n - 1)).val + 1) = s := by
  rw [ix_val_add]
  have e : s.val + n - 1 + 1 = s.val + n := by omega
  rw [e, ix_add_n, ix_self]

lemma kc_RL (n : ℕ) (hn : 0 < n) (s : Fin n) :
    ix n hn ((ix n hn (s.val + 1)).val + n - 1) = s := by
  rw [h3_ix_shift n hn _ 1 (by omega)]
  have e : s.val + 1 + (n - 1) = s.val + n := by omega
  rw [e, ix_add_n, ix_self]

lemma kc_RR (n : ℕ) (hn : 0 < n) (s : Fin n) :
    ix n hn ((ix n hn (s.val + 1)).val + 1) = ix n hn (s.val + 2) := by
  rw [ix_val_add]

lemma kc_R_inj (n : ℕ) (hn : 0 < n) (a b : Fin n)
    (h : ix n hn (a.val + 1) = ix n hn (b.val + 1)) : a = b := by
  rw [← kc_RL n hn a, ← kc_RL n hn b, h]

lemma kc_L_inj (n : ℕ) (hn : 0 < n) (a b : Fin n)
    (h : ix n hn (a.val + n - 1) = ix n hn (b.val + n - 1)) : a = b := by
  rw [← kc_LR n hn a, ← kc_LR n hn b, h]

lemma kc_R_eq_iff (n : ℕ) (hn : 0 < n) (j s : Fin n) :
    ix n hn (j.val + 1) = s ↔ j = ix n hn (s.val + n - 1) := by
  constructor
  · intro h
    rw [← h, kc_RL]
  · intro h
    rw [h, kc_LR]

lemma kc_LeqR (n : ℕ) (hn : 0 < n) (a s : Fin n)
    (h : ix n hn (a.val + n - 1) = ix n hn (s.val + 1)) : a = ix n hn (s.val + 2) := by
  rw [← kc_LR n hn a, h, kc_RR]

lemma kc_ReqL (n : ℕ) (hn : 0 < n) (a s : Fin n)
    (h : ix n hn (a.val + 1) = ix n hn (s.val + n - 1)) : s = ix n hn (a.val + 2) := by
  rw [← kc_LeqR n hn s a h.symm]

lemma kc_mc (a n : ℕ) (_hn : 0 < n) (h : a < 2 * n) :
    (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a % n = a - n) := by
  by_cases ha : a < n
  · exact Or.inl ⟨ha, Nat.mod_eq_of_lt ha⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma kc_R_ne (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) (s : Fin n) : ix n hn (s.val + 1) ≠ s := by
  intro h
  have := congrArg Fin.val h
  rw [ix_val] at this
  have hs := s.2
  rcases kc_mc (s.val + 1) n hn (by omega) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

lemma kc_par (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (a : ℕ) : (ix n hn a).val % 2 = a % 2 := by
  rw [ix_val]
  exact Nat.mod_mod_of_dvd a h2

lemma kc_mem_Iset (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) :
    x ∈ Iset n hn ↔ ∀ j : Fin n, x j * x (ix n hn (j.val + 1)) = 0 := by
  unfold Iset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, adm, markT, forall_const]
  constructor
  · intro H j
    have h := H (ix n hn (j.val + n - 1))
    rw [kc_LR, ix_val_add] at h
    have e : j.val + n - 1 + 2 = j.val + 1 + n := by omega
    rw [e, ix_add_n] at h
    exact h
  · intro H i
    have h := H (ix n hn (i.val + 1))
    rw [kc_RR] at h
    exact h

lemma kc_indR (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) (j : Fin n)
    (h : x j = 1) : x (ix n hn (j.val + 1)) = 0 := by
  have := (kc_mem_Iset n hn x).mp hx j
  rwa [h, one_mul] at this

lemma kc_indL (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) (j : Fin n)
    (h : x j = 1) : x (ix n hn (j.val + n - 1)) = 0 := by
  have := (kc_mem_Iset n hn x).mp hx (ix n hn (j.val + n - 1))
  rwa [kc_LR, h, mul_one] at this

lemma kc_ne1 (a : ZMod 2) (h : a ≠ 1) : a = 0 := by
  rcases z2_cases a with h' | h'
  · exact h'
  · exact absurd h' h

lemma kc_Iset_mono (n : ℕ) (hn : 0 < n) (x y : Fin n → ZMod 2) (hx : x ∈ Iset n hn)
    (h : ∀ j, y j = x j ∨ y j = 0) : y ∈ Iset n hn := by
  rw [kc_mem_Iset] at hx ⊢
  intro j
  rcases h j with h1 | h1
  · rcases h (ix n hn (j.val + 1)) with h3 | h3
    · rw [h1, h3]; exact hx j
    · rw [h3, mul_zero]
  · rw [h1, zero_mul]

lemma kc_Iset_set (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) (x y : Fin n → ZMod 2) (i : Fin n)
    (hx : x ∈ Iset n hn) (hL : x (ix n hn (i.val + n - 1)) = 0) (hR : x (ix n hn (i.val + 1)) = 0)
    (h : ∀ j, j ≠ i → y j = x j) : y ∈ Iset n hn := by
  rw [kc_mem_Iset] at hx ⊢
  intro j
  by_cases hj : j = i
  · subst hj
    rw [h _ (kc_R_ne n hn h2 j), hR, mul_zero]
  · rw [h j hj]
    by_cases hr : ix n hn (j.val + 1) = i
    · have := (kc_R_eq_iff n hn j i).mp hr
      rw [this, hL, zero_mul]
    · rw [h _ hr]
      exact hx j

lemma kc_tw (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw n hn (markT n) z = ∑ x ∈ Iset n hn, sgn (dot n z x) := by
  rw [tw_eq_sum]
  unfold Iset
  rw [Finset.sum_filter]
  exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun x _ => by congr)

lemma kc_upd0_keep (n : ℕ) (f : Fin n → ZMod 2) (i j : Fin n) (h : f j = 0) :
    Function.update f i 0 j = 0 := by
  by_cases hj : j = i
  · subst hj; exact Function.update_self _ _ _
  · rw [Function.update_of_ne hj]; exact h

lemma kc_nz (a : ZMod 2) (h : a ≠ 0) : a = 1 := (z2_cases a).resolve_left h

lemma kc_dot_single (n : ℕ) (z x : Fin n → ZMod 2) (s : Fin n) :
    dot n z (x + Pi.single s 1) = dot n z x + z s := by
  rw [dot_add_right]
  congr 1
  unfold dot
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

lemma kc_single_ne (n : ℕ) (s i : Fin n) (h : i ≠ s) (x : Fin n → ZMod 2) :
    (x + Pi.single s (1 : ZMod 2) : Fin n → ZMod 2) i = x i := by
  simp [Pi.single_apply, h]

lemma kc_blk_toggle (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (s s' : Fin n)
    (hp : s.val % 2 = s'.val % 2) (x : Fin n → ZMod 2) :
    blocked n hn s' (x + Pi.single s 1) ↔ blocked n hn s' x := by
  have hL : ix n hn (s'.val + n - 1) ≠ s := by
    intro h
    have := kc_par n hn h2 (s'.val + n - 1)
    rw [h] at this
    obtain ⟨m, hm⟩ := h2
    omega
  have hR : ix n hn (s'.val + 1) ≠ s := by
    intro h
    have := kc_par n hn h2 (s'.val + 1)
    rw [h] at this
    omega
  unfold blocked
  rw [kc_single_ne n s _ hL, kc_single_ne n s _ hR]

noncomputable def kc_U (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  S.filter (fun s => ¬ blocked n hn s x)

lemma kc_mem_U (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) (s : Fin n) :
    s ∈ kc_U n hn S x ↔ s ∈ S ∧ ¬ blocked n hn s x := by
  unfold kc_U
  simp only [Finset.mem_filter]

noncomputable def kc_A (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Iset n hn).filter (fun x => ¬ ∀ s ∈ S, blocked n hn s x)

lemma kc_mem_A (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    x ∈ kc_A n hn S ↔ x ∈ Iset n hn ∧ ¬ ∀ s ∈ S, blocked n hn s x := by
  unfold kc_A
  simp only [Finset.mem_filter]

lemma kc_U_toggle (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (S : Finset (Fin n)) (p : ℕ)
    (hpar : ∀ s ∈ S, s.val % 2 = p) (s : Fin n) (hs : s ∈ S) (x : Fin n → ZMod 2) :
    kc_U n hn S (x + Pi.single s 1) = kc_U n hn S x := by
  ext t
  rw [kc_mem_U, kc_mem_U]
  constructor
  · rintro ⟨ht, hb⟩
    refine ⟨ht, ?_⟩
    rwa [kc_blk_toggle n hn h2 s t (by rw [hpar s hs, hpar t ht]) x] at hb
  · rintro ⟨ht, hb⟩
    refine ⟨ht, ?_⟩
    rwa [kc_blk_toggle n hn h2 s t (by rw [hpar s hs, hpar t ht]) x]

lemma kc_U_ne (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (hx : x ∈ kc_A n hn S) : (kc_U n hn S x).Nonempty := by
  rw [kc_mem_A] at hx
  obtain ⟨s, hs, hb⟩ := not_forall₂.mp hx.2
  exact ⟨s, (kc_mem_U n hn S x s).mpr ⟨hs, hb⟩⟩

lemma kc_min_congr (n : ℕ) {T T' : Finset (Fin n)} (h : T = T') (hT : T.Nonempty)
    (hT' : T'.Nonempty) : T.min' hT = T'.min' hT' := by
  subst h
  rfl

lemma kc_unblk (n : ℕ) (hn : 0 < n) (s : Fin n) (x : Fin n → ZMod 2) (h : ¬ blocked n hn s x) :
    x (ix n hn (s.val + n - 1)) = 0 ∧ x (ix n hn (s.val + 1)) = 0 := by
  unfold blocked at h
  rw [not_or] at h
  exact ⟨kc_ne1 _ h.1, kc_ne1 _ h.2⟩

lemma kc_gmem (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (S : Finset (Fin n)) (p : ℕ)
    (hpar : ∀ s ∈ S, s.val % 2 = p) (x : Fin n → ZMod 2) (t : Fin n) (hx : x ∈ kc_A n hn S)
    (ht : t ∈ kc_U n hn S x) : x + Pi.single t 1 ∈ kc_A n hn S := by
  have h2' : 2 ≤ n := by
    obtain ⟨m, hm⟩ := h2
    omega
  rw [kc_mem_A] at hx ⊢
  rw [kc_mem_U] at ht
  have hu := kc_unblk n hn t x ht.2
  refine ⟨kc_Iset_set n hn h2' x _ t hx.1 hu.1 hu.2 (fun j hj => kc_single_ne n t j hj x), ?_⟩
  intro H
  have := H t ht.1
  rw [kc_blk_toggle n hn h2 t t rfl x] at this
  exact ht.2 this

lemma kc_sgn_flip (a : ZMod 2) : sgn a + sgn (a + 1) = 0 := by
  rcases z2_cases a with h | h <;> rw [h] <;> decide

lemma kc_inv (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (S : Finset (Fin n)) (p : ℕ)
    (hpar : ∀ s ∈ S, s.val % 2 = p) (hz : ∀ s ∈ S, z s = 1) :
    ∑ x ∈ kc_A n hn S, sgn (dot n z x) = 0 := by
  have hmem : ∀ x (hx : x ∈ kc_A n hn S),
      x + Pi.single ((kc_U n hn S x).min' (kc_U_ne n hn S x hx)) 1 ∈ kc_A n hn S :=
    fun x hx => kc_gmem n hn h2 S p hpar x _ hx (Finset.min'_mem _ _)
  refine Finset.sum_involution
    (fun x hx => x + Pi.single ((kc_U n hn S x).min' (kc_U_ne n hn S x hx)) 1) ?_ ?_ hmem ?_
  · intro x hx
    have ht := Finset.min'_mem _ (kc_U_ne n hn S x hx)
    rw [kc_mem_U] at ht
    rw [kc_dot_single, hz _ ht.1]
    exact kc_sgn_flip _
  · intro x hx _ h
    have := congrFun h ((kc_U n hn S x).min' (kc_U_ne n hn S x hx))
    rw [Pi.add_apply, Pi.single_eq_same] at this
    have h1 : (1 : ZMod 2) = 0 := add_left_cancel (this.trans (add_zero _).symm)
    exact absurd h1 (by decide)
  · intro x hx
    have ht := Finset.min'_mem _ (kc_U_ne n hn S x hx)
    rw [kc_mem_U] at ht
    rw [kc_min_congr n (kc_U_toggle n hn h2 S p hpar _ ht.1 x) _ (kc_U_ne n hn S x hx)]
    rw [add_assoc, fn_add_self, add_zero]

lemma kc_split (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (S : Finset (Fin n))
    (p : ℕ) (hpar : ∀ s ∈ S, s.val % 2 = p) (hz : ∀ s ∈ S, z s = 1) :
    tw n hn (markT n) z = ∑ x ∈ kc_B n hn S, sgn (dot n z x) := by
  rw [kc_tw]
  have hU : Iset n hn = kc_B n hn S ∪ kc_A n hn S := by
    ext x
    simp only [Finset.mem_union, kc_mem_B, kc_mem_A]
    tauto
  have hD : Disjoint (kc_B n hn S) (kc_A n hn S) := by
    rw [Finset.disjoint_left]
    intro x h1 h3
    rw [kc_mem_B] at h1
    rw [kc_mem_A] at h3
    exact h3.2 h1.2
  rw [hU, Finset.sum_union hD, kc_inv n hn h2 z S p hpar hz, add_zero]

lemma tw_abs_le (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (p : ℕ) :
    |tw n hn (markT n) z| ≤
      (cntB n hn (Finset.univ.filter (fun s => z s ≠ 0 ∧ s.val % 2 = p)) : ℤ) := by
  have hp1 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0 ∧ s.val % 2 = p), s.val % 2 = p := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact hs.2.2
  have hp2 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0 ∧ s.val % 2 = p), z s = 1 := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact kc_nz _ hs.2.1
  rw [kc_split n hn h2 z _ p hp1 hp2, kc_cntB]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rcases z2_cases (dot n z x) with h | h <;> rw [h] <;> decide

lemma kc_dot0 (n : ℕ) (hn : 0 < n) (z x : Fin n → ZMod 2)
    (hx : x ∈ kc_B n hn (Finset.univ.filter (fun s => z s ≠ 0))) : dot n z x = 0 := by
  rw [kc_mem_B] at hx
  unfold dot
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : z i = 0
  · rw [hi, zero_mul]
  have hb := hx.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  rcases z2_cases (x i) with h | h
  · rw [h, mul_zero]
  exfalso
  rcases hb with hb | hb
  · rw [kc_indL n hn x hx.1 i h] at hb
    exact absurd hb (by decide)
  · rw [kc_indR n hn x hx.1 i h] at hb
    exact absurd hb (by decide)

lemma tw_pure (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (p : ℕ)
    (hz : ∀ s, z s ≠ 0 → s.val % 2 = p) :
    tw n hn (markT n) z = (cntB n hn (Finset.univ.filter (fun s => z s ≠ 0)) : ℤ) := by
  have hp1 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0), s.val % 2 = p := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact hz s hs.2
  have hp2 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0), z s = 1 := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact kc_nz _ hs.2
  rw [kc_split n hn h2 z _ p hp1 hp2, kc_cntB]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun x hx => by rw [kc_dot0 n hn z x hx]; rfl)]
  simp

lemma cntB_anti (n : ℕ) (hn : 0 < n) (S T : Finset (Fin n)) (h : S ⊆ T) :
    cntB n hn T ≤ cntB n hn S := by
  rw [kc_cntB, kc_cntB]
  apply Finset.card_le_card
  intro x hx
  rw [kc_mem_B] at hx ⊢
  exact ⟨hx.1, fun s hs => hx.2 s (h hs)⟩

lemma kc_clr_val (n : ℕ) (f : Fin n → ZMod 2) (a b j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) :
    Function.update (Function.update f a 0) b 0 j = f j := by
  rw [Function.update_of_ne hjb, Function.update_of_ne hja]

lemma kc_val_ix (n : ℕ) (hn : 0 < n) (a : Fin n) (b : ℕ) (h : a = ix n hn b) : a.val = b % n := by
  rw [h, ix_val]

lemma kc_B_maps (n : ℕ) (hn : 0 < n) (s : Fin n) (S' : Finset (Fin n)) (hs : s ∉ S')
    (hsp : ∀ t ∈ S', t.val ≠ (s.val + 2) % n ∧ s.val ≠ (t.val + 2) % n)
    (x : Fin n → ZMod 2) (hx : x ∈ kc_B n hn (insert s S')) :
    Function.update (Function.update x (ix n hn (s.val + n - 1)) 0) (ix n hn (s.val + 1)) 0 ∈
      kc_B n hn S' \ kc_B n hn (insert s S') := by
  rw [kc_mem_B] at hx
  rw [Finset.mem_sdiff, kc_mem_B, kc_mem_B]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply kc_Iset_mono n hn x _ hx.1
    intro j
    by_cases hR : j = ix n hn (s.val + 1)
    · right
      rw [hR, Function.update_self]
    by_cases hL : j = ix n hn (s.val + n - 1)
    · right
      rw [Function.update_of_ne hR, hL, Function.update_self]
    · left
      exact kc_clr_val n x _ _ j hL hR
  · intro t ht
    have hb := hx.2 t (Finset.mem_insert_of_mem ht)
    have hts : t ≠ s := fun h => hs (h ▸ ht)
    have hLL : ix n hn (t.val + n - 1) ≠ ix n hn (s.val + n - 1) :=
      fun h => hts (kc_L_inj n hn t s h)
    have hLR : ix n hn (t.val + n - 1) ≠ ix n hn (s.val + 1) :=
      fun h => (hsp t ht).1 (kc_val_ix n hn _ _ (kc_LeqR n hn t s h))
    have hRL : ix n hn (t.val + 1) ≠ ix n hn (s.val + n - 1) :=
      fun h => (hsp t ht).2 (kc_val_ix n hn _ _ (kc_ReqL n hn t s h))
    have hRR : ix n hn (t.val + 1) ≠ ix n hn (s.val + 1) :=
      fun h => hts (kc_R_inj n hn t s h)
    unfold blocked at hb ⊢
    rw [kc_clr_val n x _ _ _ hLL hLR, kc_clr_val n x _ _ _ hRL hRR]
    exact hb
  · intro H
    have h := H.2 s (Finset.mem_insert_self _ _)
    unfold blocked at h
    rw [Function.update_self,
      kc_upd0_keep n _ _ _ (Function.update_self _ _ _)] at h
    rcases h with h | h <;> exact absurd h (by decide)

lemma kc_step (n : ℕ) (hn : 0 < n) (s : Fin n) (S' : Finset (Fin n)) (hs : s ∉ S')
    (hsp : ∀ t ∈ S', t.val ≠ (s.val + 2) % n ∧ s.val ≠ (t.val + 2) % n) :
    5 * cntB n hn (insert s S') ≤ 4 * cntB n hn S' := by
  classical
  rw [kc_cntB, kc_cntB]
  have hsub : kc_B n hn (insert s S') ⊆ kc_B n hn S' := by
    intro x hx
    rw [kc_mem_B] at hx ⊢
    exact ⟨hx.1, fun t ht => hx.2 t (Finset.mem_insert_of_mem ht)⟩
  have hinj : (kc_B n hn (insert s S')).card ≤
      ((kc_B n hn S' \ kc_B n hn (insert s S')) ×ˢ
        (Finset.univ : Finset (ZMod 2 × ZMod 2))).card := by
    apply Finset.card_le_card_of_injOn (fun x => (Function.update (Function.update x
      (ix n hn (s.val + n - 1)) 0) (ix n hn (s.val + 1)) 0,
      (x (ix n hn (s.val + n - 1)), x (ix n hn (s.val + 1)))))
    · intro x hx
      rw [Finset.mem_coe] at hx
      rw [Finset.mem_coe, Finset.mem_product]
      exact ⟨kc_B_maps n hn s S' hs hsp x hx, Finset.mem_univ _⟩
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      funext j
      by_cases hR : j = ix n hn (s.val + 1)
      · rw [hR]
        exact h3
      by_cases hL : j = ix n hn (s.val + n - 1)
      · rw [hL]
        exact h2
      have := congrFun h1 j
      rwa [kc_clr_val n x _ _ j hL hR, kc_clr_val n y _ _ j hL hR] at this
  rw [Finset.card_product, Finset.card_univ, Finset.card_sdiff_of_subset hsub] at hinj
  have h4 : Fintype.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Fintype.card_prod, ZMod.card]
  rw [h4] at hinj
  have := Finset.card_le_card hsub
  omega

lemma kc_B_empty (n : ℕ) (hn : 0 < n) : kc_B n hn ∅ = Iset n hn := by
  ext x
  rw [kc_mem_B]
  simp

lemma decay (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (S : Finset (Fin n))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s'.val ≠ (s.val + 2) % n) :
    5 ^ S.card * cntB n hn S ≤ 4 ^ S.card * (Iset n hn).card := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [kc_cntB, kc_B_empty]; simp
  | insert s S' hs ih =>
    have hS' : ∀ a ∈ S', ∀ b ∈ S', b.val ≠ (a.val + 2) % n := fun a ha b hb =>
      hS a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    have hI := ih hS'
    have hstep := kc_step n hn s S' hs (fun t ht =>
      ⟨hS s (Finset.mem_insert_self _ _) t (Finset.mem_insert_of_mem ht),
       hS t (Finset.mem_insert_of_mem ht) s (Finset.mem_insert_self _ _)⟩)
    rw [Finset.card_insert_of_notMem hs, pow_succ, pow_succ]
    calc 5 ^ S'.card * 5 * cntB n hn (insert s S')
        = 5 ^ S'.card * (5 * cntB n hn (insert s S')) := by ring
      _ ≤ 5 ^ S'.card * (4 * cntB n hn S') := Nat.mul_le_mul_left _ hstep
      _ = 4 * (5 ^ S'.card * cntB n hn S') := by ring
      _ ≤ 4 * (4 ^ S'.card * (Iset n hn).card) := Nat.mul_le_mul_left _ hI
      _ = 4 ^ S'.card * 4 * (Iset n hn).card := by ring

lemma kc_card_upd (n : ℕ) (A : Finset (Fin n → ZMod 2)) (i : Fin n) (a : ZMod 2) :
    A.card ≤ 2 * (A.image (fun x => Function.update x i a)).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro b _
  calc (A.filter (fun x => Function.update x i a = b)).card
      ≤ ({Function.update b i 0, Function.update b i 1} : Finset (Fin n → ZMod 2)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        have hx' : x = Function.update b i (x i) := by
          rw [← hx.2, Function.update_idem, Function.update_eq_self]
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases z2_cases (x i) with h | h
        · left
          rw [hx', h]
        · right
          rw [hx', h]
    _ ≤ 2 := Finset.card_le_two

lemma kc_upd0_mem (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) (i : Fin n) (hx : x ∈ Iset n hn) :
    Function.update x i 0 ∈ Iset n hn := by
  apply kc_Iset_mono n hn x _ hx
  intro j
  by_cases hj : j = i
  · right
    rw [hj, Function.update_self]
  · left
    exact Function.update_of_ne hj _ _

lemma kc_low_mem (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (s s' : Fin n) (h1 : s ≠ s')
    (h2 : s'.val ≠ (s.val + 2) % n) (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) :
    Function.update (Function.update (Function.update (Function.update (Function.update x
      (ix n hn (s'.val + n - 1)) 0) (ix n hn (s'.val + 1)) 0) s 0) (ix n hn (s.val + 2)) 0)
      (ix n hn (s.val + 1)) 1 ∈ kc_B n hn {s} \ kc_B n hn {s, s'} := by
  set w := Function.update (Function.update (Function.update (Function.update x
      (ix n hn (s'.val + n - 1)) 0) (ix n hn (s'.val + 1)) 0) s 0) (ix n hn (s.val + 2)) 0
    with hw
  have hwI : w ∈ Iset n hn :=
    kc_upd0_mem n hn _ _ (kc_upd0_mem n hn _ _ (kc_upd0_mem n hn _ _ (kc_upd0_mem n hn _ _ hx)))
  have wL : w (ix n hn (s'.val + n - 1)) = 0 :=
    kc_upd0_keep n _ _ _ (kc_upd0_keep n _ _ _ (kc_upd0_keep n _ _ _ (Function.update_self _ _ _)))
  have wR : w (ix n hn (s'.val + 1)) = 0 :=
    kc_upd0_keep n _ _ _ (kc_upd0_keep n _ _ _ (Function.update_self _ _ _))
  have ws : w s = 0 := kc_upd0_keep n _ _ _ (Function.update_self _ _ _)
  have ws2 : w (ix n hn (s.val + 2)) = 0 := Function.update_self _ _ _
  have hyI : Function.update w (ix n hn (s.val + 1)) 1 ∈ Iset n hn := by
    apply kc_Iset_set n hn (by omega) w _ (ix n hn (s.val + 1)) hwI
    · rw [kc_RL]; exact ws
    · rw [kc_RR]; exact ws2
    · intro j hj
      exact Function.update_of_ne hj _ _
  have hne1 : ix n hn (s'.val + n - 1) ≠ ix n hn (s.val + 1) :=
    fun h => h2 (kc_val_ix n hn _ _ (kc_LeqR n hn s' s h))
  have hne2 : ix n hn (s'.val + 1) ≠ ix n hn (s.val + 1) :=
    fun h => h1 (kc_R_inj n hn s' s h).symm
  rw [Finset.mem_sdiff, kc_mem_B, kc_mem_B]
  refine ⟨⟨hyI, ?_⟩, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    right
    exact Function.update_self _ _ _
  · intro H
    have hb := H.2 s' (by simp)
    unfold blocked at hb
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2, wL, wR] at hb
    rcases hb with hb | hb <;> exact absurd hb (by decide)

lemma lower32 (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (s s' : Fin n) (h1 : s ≠ s')
    (h2 : s'.val ≠ (s.val + 2) % n) :
    (Iset n hn).card ≤ 32 * (cntB n hn {s} - cntB n hn {s, s'}) := by
  classical
  have c1 := kc_card_upd n (Iset n hn) (ix n hn (s'.val + n - 1)) 0
  have c2 := kc_card_upd n ((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)) (ix n hn (s'.val + 1)) 0
  have c3 := kc_card_upd n (((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)) s 0
  have c4 := kc_card_upd n ((((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)).image
    (fun x => Function.update x s 0)) (ix n hn (s.val + 2)) 0
  have c5 := kc_card_upd n (((((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)).image
    (fun x => Function.update x s 0)).image
    (fun x => Function.update x (ix n hn (s.val + 2)) 0)) (ix n hn (s.val + 1)) 1
  have hsub : ((((((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)).image
    (fun x => Function.update x s 0)).image
    (fun x => Function.update x (ix n hn (s.val + 2)) 0)).image
    (fun x => Function.update x (ix n hn (s.val + 1)) 1)) ⊆
      kc_B n hn {s} \ kc_B n hn {s, s'} := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨w4, ⟨w3, ⟨w2, ⟨w1, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hy
    exact kc_low_mem n hn h6 s s' h1 h2 x hx
  have hsub2 : kc_B n hn {s, s'} ⊆ kc_B n hn {s} := by
    intro x hx
    rw [kc_mem_B] at hx ⊢
    exact ⟨hx.1, fun t ht => hx.2 t (by rw [Finset.mem_singleton] at ht; simp [ht])⟩
  rw [kc_cntB, kc_cntB, ← Finset.card_sdiff_of_subset hsub2]
  have := Finset.card_le_card hsub
  omega

lemma kc_tau_R (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : m ≤ n) (j : Fin n) :
    h3_shift n hn m hm (ix n hn (j.val + 1)) = ix n hn ((h3_shift n hn m hm j).val + 1) := by
  show ix n hn ((ix n hn (j.val + 1)).val + m) = ix n hn ((ix n hn (j.val + m)).val + 1)
  rw [ix_val_add, ix_val_add, add_right_comm]

lemma kc_taui_R (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : m ≤ n) (j : Fin n) :
    (h3_shift n hn m hm).symm (ix n hn (j.val + 1)) =
      ix n hn (((h3_shift n hn m hm).symm j).val + 1) := by
  show ix n hn ((ix n hn (j.val + 1)).val + n - m) = ix n hn ((ix n hn (j.val + n - m)).val + 1)
  rw [h3_ix_shift n hn _ m hm, ix_val_add]
  congr 1
  omega

lemma kc_Iset_comp (n : ℕ) (hn : 0 < n) (σ : Fin n ≃ Fin n)
    (hσ : ∀ j : Fin n, σ (ix n hn (j.val + 1)) = ix n hn ((σ j).val + 1))
    (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) : x ∘ σ ∈ Iset n hn := by
  rw [kc_mem_Iset] at hx ⊢
  intro j
  simp only [Function.comp]
  rw [hσ]
  exact hx (σ j)

lemma tw_rot (n : ℕ) (hn : 0 < n) (k : ℕ) (z : Fin n → ZMod 2) :
    tw n hn (markT n) (rot n hn k z) = tw n hn (markT n) z := by
  have hm : k % n ≤ n := Nat.le_of_lt (Nat.mod_lt _ hn)
  have hr : rot n hn k z = z ∘ (h3_shift n hn (k % n) hm).symm := rfl
  rw [hr, kc_tw, kc_tw]
  refine Finset.sum_nbij' (fun x => x ∘ (h3_shift n hn (k % n) hm))
    (fun y => y ∘ (h3_shift n hn (k % n) hm).symm) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact kc_Iset_comp n hn _ (kc_tau_R n hn _ hm) x hx
  · intro y hy
    exact kc_Iset_comp n hn _ (kc_taui_R n hn _ hm) y hy
  · intro x _
    funext i
    simp
  · intro y _
    funext i
    simp
  · intro x _
    congr 1
    unfold dot
    rw [← Equiv.sum_comp (h3_shift n hn (k % n) hm)]
    simp

lemma kc_small_r (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (k r : ℕ)
    (hk : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = r ∧ s.val + 2 < n)).card) :
    5 ^ k * |tw n hn (markT n) z| ≤ 4 ^ k * ((Iset n hn).card : ℤ) := by
  obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq hk
  have hmem : ∀ s ∈ S, z s ≠ 0 ∧ s.val % 4 = r ∧ s.val + 2 < n := by
    intro s hs
    have := hS hs
    rw [Finset.mem_filter] at this
    exact this.2
  have hdec := decay n hn h6 S (by
    intro a ha b hb heq
    have h3 := hmem a ha
    have h4 := hmem b hb
    rw [Nat.mod_eq_of_lt (by omega)] at heq
    omega)
  have hsub : S ⊆ Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 2 = r % 2) := by
    intro s hs
    rw [Finset.mem_filter]
    have := hmem s hs
    exact ⟨Finset.mem_univ _, this.1, by omega⟩
  have hab := tw_abs_le n hn h2 z (r % 2)
  have hanti := cntB_anti n hn _ _ hsub
  rw [hc] at hdec
  have hd : (5 : ℤ) ^ k * (cntB n hn S : ℤ) ≤ 4 ^ k * ((Iset n hn).card : ℤ) := by
    exact_mod_cast hdec
  calc (5 : ℤ) ^ k * |tw n hn (markT n) z|
      ≤ 5 ^ k * (cntB n hn (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 2 = r % 2)) : ℤ) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ 5 ^ k * (cntB n hn S : ℤ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hanti) (by positivity)
    _ ≤ _ := hd

lemma kc_T_card (n : ℕ) :
    (Finset.univ.filter (fun s : Fin n => n ≤ s.val + 2)).card ≤ 2 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun s : Fin n => n ≤ s.val + 2)) (t := Finset.range 2) (fun s : Fin n => s.val + 2 - n)
    (by
      intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs
      rw [Finset.mem_coe, Finset.mem_range]
      have := s.2
      show s.val + 2 - n < 2
      omega)
    (by
      intro s hs t ht hst
      rw [Finset.mem_coe, Finset.mem_filter] at hs ht
      simp only at hst
      apply Fin.ext
      omega)
  simpa using h

lemma kc_wt_le (n : ℕ) (z : Fin n → ZMod 2) :
    wt n z ≤ (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 0 ∧ s.val + 2 < n)).card +
      (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 1 ∧ s.val + 2 < n)).card +
      (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 2 ∧ s.val + 2 < n)).card +
      (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 3 ∧ s.val + 2 < n)).card + 2 := by
  classical
  have hT := kc_T_card n
  unfold wt
  refine le_trans (Finset.card_le_card (t :=
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 0 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 1 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 2 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 3 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => n ≤ s.val + 2))) ?_) ?_
  · intro s hs
    rw [Finset.mem_filter] at hs
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : s.val + 2 < n
    · have h4 : s.val % 4 = 0 ∨ s.val % 4 = 1 ∨ s.val % 4 = 2 ∨ s.val % 4 = 3 := by omega
      rcases h4 with h4 | h4 | h4 | h4 <;> simp [hs.2, h4, hlt]
    · right
      omega
  · refine le_trans (Finset.card_union_le _ _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Finset.card_union_le _ _) _) _) _) ?_
    omega

lemma tw_small (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (k : ℕ)
    (hz : 4 * k + 2 ≤ wt n z) :
    5 ^ k * |tw n hn (markT n) z| ≤ 4 ^ k * ((Iset n hn).card : ℤ) := by
  have hw := kc_wt_le n z
  by_cases c0 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 0 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 0 c0
  by_cases c1 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 1 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 1 c1
  by_cases c2 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 2 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 2 c2
  by_cases c3 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 3 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 3 c3
  omega
def cl_gg (c : C4) (a : ℕ) : ZMod 2 :=
  c.1 * h3_b 0 a + c.2.1 * h3_b 1 a + c.2.2.1 * h3_b 2 a + c.2.2.2 * h3_b 3 a

lemma cl_gg_mod (c : C4) (a : ℕ) : cl_gg c (a % 6) = cl_gg c a := by
  unfold cl_gg
  rw [h3_b_mod, h3_b_mod, h3_b_mod, h3_b_mod]

lemma cl_gg_congr (c : C4) (a b : ℕ) (h : a % 6 = b % 6) : cl_gg c a = cl_gg c b := by
  rw [← cl_gg_mod c a, ← cl_gg_mod c b, h]

lemma cl_bc_ix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (c : C4) (a : ℕ) :
    bc n c (ix n hn a) = cl_gg c a := by
  unfold bc cl_gg
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3_base_ix n hn h6]

lemma cl_bc_apply (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (c : C4) (i : Fin n) :
    bc n c i = cl_gg c i.val := by
  rw [← cl_bc_ix n hn h6, ix_self]

lemma cl_bc_zero (n : ℕ) : bc n 0 = 0 := by
  unfold bc
  funext i
  simp

lemma cl_pat : ∀ c : C4, c ≠ 0 → ∃ r1 r2 : Fin 6, r1 ≠ r2 ∧ cl_gg c r1.val ≠ 0 ∧
    cl_gg c r2.val ≠ 0 := by
  unfold cl_gg h3_b
  decide

lemma cl_shift : ∀ c : C4, ∀ d : Fin 6, ∃ c' : C4, ∀ r : Fin 6,
    cl_gg c' r.val = cl_gg c (r.val + 6 - d.val) := by
  unfold cl_gg h3_b
  decide

lemma cl_wt_tri (n : ℕ) (a b : Fin n → ZMod 2) : wt n a ≤ wt n (a + b) + wt n b := by
  unfold wt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_cases hb : b i = 0
  · left
    rw [hb, add_zero]
    exact hi
  · right
    exact hb

lemma cl_wt_es0 (n : ℕ) (hn : 0 < n) : wt n (es n 0) ≤ 1 := by
  unfold wt
  have h : Finset.univ.filter (fun i => es n 0 i ≠ 0) ⊆ {(⟨0, hn⟩ : Fin n)} := by
    intro i hi
    have hi2 := (Finset.mem_filter.1 hi).2
    simp only [Finset.mem_singleton, Fin.ext_iff]
    by_contra h
    exact hi2 (by simp only [es]; exact if_neg h)
  exact le_trans (Finset.card_le_card h) (by simp)

lemma cl_wt_bc (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (c : C4) (hc : c ≠ 0) :
    2 * t ≤ wt n (bc n c) := by
  have h6 : 6 ∣ n := ⟨t, hnt⟩
  obtain ⟨r1, r2, hr, h1, h2⟩ := cl_pat c hc
  have hr' : r1.val ≠ r2.val := fun h => hr (Fin.ext h)
  have r1l := r1.isLt
  have r2l := r2.isLt
  let g : ℕ → ℕ := fun k => if k < t then 6 * k + r1.val else 6 * (k - t) + r2.val
  have hg : ∀ k ∈ Finset.range (2 * t), g k < n := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [g]
    split_ifs <;> omega
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range (2 * t))
    (t := Finset.univ.filter (fun i => bc n c i ≠ 0)) (fun k => ix n hn (g k)) ?_ ?_
  · rw [Finset.card_range] at hcard
    exact hcard
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [cl_bc_ix n hn h6]
    simp only [g]
    split_ifs
    · rw [cl_gg_congr c _ r1.val (by omega)]
      exact h1
    · rw [cl_gg_congr c _ r2.val (by omega)]
      exact h2
  · intro k hk k' hk' he
    have a1 := hg k hk
    have a2 := hg k' hk'
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    have := (ix_eq_iff n hn _ _).1 he
    rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2] at this
    simp only [g] at this
    split_ifs at this <;> omega

lemma cl_rot_add (n : ℕ) (hn : 0 < n) (k : ℕ) (a b : Fin n → ZMod 2) :
    rot n hn k (a + b) = rot n hn k a + rot n hn k b := by
  funext i
  rfl

lemma cl_rot_bc (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (k : ℕ) (c : C4) :
    ∃ c' : C4, bc n c' = rot n hn k (bc n c) ∧ ∀ r : Fin 6,
      cl_gg c' r.val = cl_gg c (r.val + 6 - k % 6) := by
  obtain ⟨c', hc'⟩ := cl_shift c ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩
  refine ⟨c', ?_, hc'⟩
  funext i
  unfold rot
  rw [cl_bc_apply n hn h6, cl_bc_ix n hn h6]
  have hkn : k % n < n := Nat.mod_lt _ hn
  have hk6 : k % n % 6 = k % 6 := Nat.mod_mod_of_dvd k h6
  obtain ⟨t, ht⟩ := h6
  rw [← cl_gg_mod c' i.val]
  have hi6 := hc' ⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩
  simp only at hi6
  rw [hi6]
  apply cl_gg_congr
  have := i.isLt
  omega


abbrev Words (n : ℕ) := Fin n → ZMod 2
abbrev PredMap (n : ℕ) := Words n →ₗ[ZMod 2] Words n
abbrev Probe (n : ℕ) := Words n →ₗ[ZMod 2] ZMod 2

def pinVec {n : ℕ} (a : Fin n) : Words n := fun i => if i = a then 1 else 0

lemma dot_pinVec {n : ℕ} (a : Fin n) (w : Words n) : dot n (pinVec a) w = w a := by
  simp [dot, pinVec, ite_mul]

def pinProbe {n h : ℕ} (hn : 0 < n) (sites : Fin h → Fin n) (j : Fin h) : Probe n :=
  (LinearMap.proj (sites j)).comp (mixL n hn)

def pinKer {n h : ℕ} (hn : 0 < n) (sites : Fin h → Fin n) : Submodule (ZMod 2) (Words n) :=
  LinearMap.ker (LinearMap.pi (pinProbe hn sites))

noncomputable def pinDual {n h : ℕ} (sites : Fin h → Fin n) : Submodule (ZMod 2) (Words n) :=
  Submodule.span (ZMod 2) (Set.range (base n)) ⊔
    Submodule.span (ZMod 2) (Set.range (fun j => pinVec (sites j)))

lemma mem_pinKer {n h : ℕ} (hn : 0 < n) (sites : Fin h → Fin n) (w : Words n) :
    w ∈ pinKer hn sites ↔ ∀ j, mix n hn w (sites j) = 0 := by
  rw [pinKer, LinearMap.mem_ker]
  exact ⟨fun p j => congrFun p j, fun p => funext p⟩

lemma pinKer_run {n h : ℕ} (hn : 0 < n) (sites : Fin h → Fin n) (w w₀ : Words n) :
    run n h (fun j _ => pinProbe hn sites j) w = run n h (fun j _ => pinProbe hn sites j) w₀ ↔
      w - w₀ ∈ pinKer hn sites := by
  obtain ⟨p,hp⟩ := run_eq_iff n h (fun j _ => pinProbe hn sites j) w₀
  rw [hp, mem_pinKer]
  rfl

lemma pin_mix_orth {n h : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (sites : Fin h → Fin n) :
    orth n ((mixL n hn).comp (pinKer hn sites).subtype) = pinDual sites := by
  apply h6_orth_eq n hn h6 h (pinDual sites) _ (fun j => pinVec (sites j)) _ le_rfl (pinProbe hn sites)
  · intro j w
    rw [dot_pinVec]
    rfl
  · intro j
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨j,rfl⟩)
  · intro j
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨j,rfl⟩)

lemma pin_tau_orth {n h : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (sites : Fin h → Fin n) :
    orth n (h5_tau n hn (pinKer hn sites)) = pinDual sites := by
  apply le_antisymm
  · rw [← pin_mix_orth hn h6 sites]
    intro z hz
    rw [mem_orth] at hz ⊢
    intro u
    show dot n z (mix n hn u.1) = 0
    have h1 := hz (u,0)
    rw [h5_tau_apply] at h1
    simp only [ZeroMemClass.coe_zero, mix_zero, add_zero] at h1
    have hb (j) : dot n (base n j) (mix n hn u.1 + even n (mix n hn u.1)) = 0 := by
      rw [dot_add_right, base_dot_mix n hn h6, ← dot_even]
      rcases even_base n j with a | a
      · rw [a, base_dot_mix n hn h6, add_zero]
      · rw [a, dot_zero_left, add_zero]
    obtain ⟨w,hw⟩ := mix_surj n hn h6 _ hb
    have hkw : w ∈ pinKer hn sites := by
      rw [mem_pinKer]
      intro j
      have hu := (mem_pinKer hn sites u.1).mp u.2 j
      rw [hw, Pi.add_apply, even_apply, hu]
      simp
    have hz' : w ∈ h5_KZ n hn (pinKer hn sites) := by
      rw [h5_mem_KZ]
      refine ⟨hkw, ?_⟩
      rw [hw, even_add, even_even, fn_add_self]
    have h2 := hz (0,⟨w,hz'⟩)
    rw [h5_tau_apply] at h2
    simp only [ZeroMemClass.coe_zero, mix_zero, even_zero, zero_add] at h2
    rw [hw, dot_add_right, h1, add_zero] at h2
    exact h2
  · unfold pinDual
    refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨j,rfl⟩
      exact h5_base_mem n hn h6 _ j
    · rintro _ ⟨j,rfl⟩
      rw [SetLike.mem_coe, mem_orth]
      intro u
      have hu := (mem_pinKer hn sites _).mp u.1.2 j
      have hv := (mem_pinKer hn sites _).mp ((h5_mem_KZ n hn _ _).mp u.2.2).1 j
      rw [h5_tau_apply, dot_add_right, dot_pinVec, dot_pinVec, even_apply, hu, hv]
      simp

lemma card_subfiber {α β : Type} (P : α → Prop) (C G : β → Prop) (e : α ≃ {y // C y})
    (he : ∀ a, P a ↔ G (e a).val) :
    Nat.card {a // P a} = Nat.card {y // G y ∧ C y} := by
  let e' : {a // P a} ≃ {y : {y // C y} // G y.val} := e.subtypeEquiv he
  apply Nat.card_congr
  refine e'.trans
    { toFun := fun w => ⟨w.val.val, w.2, w.val.2⟩
      invFun := fun w => ⟨⟨w.val,w.2.2⟩,w.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma pinUpper {n h : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (sites : Fin h → Fin n)
    (name c : Words n) (A : ℕ → PredMap n) (b : ℕ → Words n) :
    (Nat.card {w : Words n // out n hn name c w =
      A (run n h (fun j _ => pinProbe hn sites j) w) w + b (run n h (fun j _ => pinProbe hn sites j) w)} : ℤ)
      ≤ Ssum n hn (fun _ => true) (pinDual sites) := by
  let R := run n h (fun j _ => pinProbe hn sites j)
  let G := fun w : Words n => out n hn name c w = A (R w) w + b (R w)
  change (Nat.card {w : Words n // G w} : ℤ) ≤ _
  by_contra hnle
  have hW : (Nat.card (Words n) : ℤ) = 2^n := by simp [Words, Nat.card_eq_fintype_card]
  refine h6_fiber_sum R G (fun w₀ => ?_)
  let K := pinKer hn sites
  have hR (w : Words n) : R w = R w₀ ↔ w - w₀ ∈ K := pinKer_run hn sites w w₀
  have hr (u : K) : R (w₀ + u.val) = R w₀ := (hR _).mpr (by rw [add_sub_cancel_left]; exact u.2)
  let e : K ≃ {w : Words n // R w = R w₀} :=
    { toFun := fun u => ⟨w₀+u.val,hr u⟩
      invFun := fun w => ⟨w.val-w₀,(hR _).mp w.2⟩
      left_inv := fun _ => Subtype.ext (add_sub_cancel_left _ _)
      right_inv := fun _ => Subtype.ext (add_sub_cancel _ _) }
  have ek : Nat.card {u : K // ∀ i, (true : Bool) = true →
      out n hn name c (w₀+u.val) i = (A (R w₀) (w₀+u.val) + b (R w₀)) i} =
      Nat.card {w : Words n // G w ∧ R w = R w₀} := by
    refine card_subfiber _ (fun w => R w = R w₀) G e (fun u => ?_)
    change _ ↔ out n hn name c (w₀+u.val) = A (R (w₀+u.val)) (w₀+u.val) + b (R (w₀+u.val))
    rw [hr]
    exact ⟨fun v => funext fun i => v i rfl, fun v i _ => congrFun v i⟩
  have hc := gl_cell_count n hn h6 (fun _ => true) name c K w₀ (A (R w₀)) (b (R w₀))
  rw [ek, show orth n (h5_tau n hn K) = pinDual sites from pin_tau_orth hn h6 sites,
    Nat.card_congr e] at hc
  rw [hW]
  have hh : Ssum n hn (fun _ => true) (pinDual sites) ≤ (Nat.card {w : Words n // G w} : ℤ)-1 := by omega
  exact le_trans hc (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _))

lemma pinLower {n h : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (sites : Fin h → Fin n)
    (name c : Words n) :
    ∃ (A : ℕ → PredMap n) (b : ℕ → Words n),
      (Nat.card {w : Words n // out n hn name c w =
        A (run n h (fun j _ => pinProbe hn sites j) w) w +
        b (run n h (fun j _ => pinProbe hn sites j) w)} : ℤ) =
          Ssum n hn (fun _ => true) (pinDual sites) := by
  let K := pinKer hn sites
  let R := run n h (fun j _ => pinProbe hn sites j)
  obtain ⟨A,b,hAb⟩ := nonadaptive_count n hn h (fun _ => true) name c (pinProbe hn sites)
  refine ⟨A,b,?_⟩
  have e : Nat.card {w : Words n // ∀ i, (true : Bool) = true →
      out n hn name c w i = (A (R w) w + b (R w)) i} =
      Nat.card {w : Words n // out n hn name c w = A (R w) w + b (R w)} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ =>
      ⟨fun v => funext fun i => v i rfl, fun v i _ => congrFun v i⟩)
  rw [e] at hAb
  have hf := fourier_count n hn (fun _ => true) ((mixL n hn).comp K.subtype)
  rw [show orth n ((mixL n hn).comp K.subtype) = pinDual sites from pin_mix_orth hn h6 sites] at hf
  have ez := congrArg (fun k : ℕ => (k : ℤ)) hAb
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at ez
  exact mul_left_cancel₀ (a := (Nat.card K : ℤ)) (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (ez.trans hf)

def feasible {n h : ℕ} (hn : 0 < n) (sites : Fin h → Fin n) (name c : Words n)
    (fixed : Bool) (k : ℕ) : Prop :=
  ∃ (ask : Fin h → ℕ → Probe n) (A : ℕ → PredMap n) (b : ℕ → Words n),
    (fixed = true → ∀ j p w, ask j p w = mix n hn w (sites j)) ∧
      k ≤ Nat.card {w : Words n // out n hn name c w = A (run n h ask w) w + b (run n h ask w)}

lemma fixed_geometry {n h : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (sites : Fin h → Fin n)
    (name c : Words n) (k : ℕ) :
    feasible hn sites name c true k ↔ (k : ℤ) ≤ Ssum n hn (fun _ => true) (pinDual sites) := by
  constructor
  · rintro ⟨ask,A,b,ha,hk⟩
    have e : ask = fun j _ => pinProbe hn sites j := by
      funext j p
      exact LinearMap.ext (ha rfl j p)
    subst e
    exact le_trans (Nat.cast_le.mpr hk) (pinUpper hn h6 sites name c A b)
  · intro hk
    obtain ⟨A,b,he⟩ := pinLower hn h6 sites name c
    exact ⟨fun j _ => pinProbe hn sites j,A,b,fun _ _ _ _ => rfl,Nat.cast_le.mp (hk.trans_eq he.symm)⟩

lemma adaptive_geometry {n h : ℕ} (hn : 0 < n) (h6 : 6 ∣ n) (sites : Fin h → Fin n)
    (name c : Words n) (k : ℕ) :
    feasible hn sites name c false k ↔
      ∃ D : Submodule (ZMod 2) (Words n), (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
        Module.finrank (ZMod 2) D ≤ h+4 ∧ (k : ℤ) ≤ Ssum n hn (fun _ => true) D := by
  constructor
  · rintro ⟨ask,A,b,_,hk⟩
    obtain ⟨D,hb,he,hd,hD⟩ := upper n hn h6 h (fun _ => true) name c ask A b
    have ee : Nat.card {w : Words n // ∀ i, (true : Bool) = true → out n hn name c w i =
        (A (run n h ask w) w + b (run n h ask w)) i} =
        Nat.card {w : Words n // out n hn name c w = A (run n h ask w) w + b (run n h ask w)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun _ =>
        ⟨fun v => funext fun i => v i rfl, fun v i _ => congrFun v i⟩))
    rw [ee] at hD
    exact ⟨D,hb,he,hd,(Nat.cast_le.mpr hk).trans hD⟩
  · rintro ⟨D,hb,he,hd,hk⟩
    obtain ⟨ask,A,b,_,hD⟩ := lower n hn h6 h (fun _ => true) name c D hb he hd
    have ee : Nat.card {w : Words n // ∀ i, (true : Bool) = true → out n hn name c w i =
        (A (run n h ask w) w + b (run n h ask w)) i} =
        Nat.card {w : Words n // out n hn name c w = A (run n h ask w) w + b (run n h ask w)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun _ =>
        ⟨fun v => funext fun i => v i rfl, fun v i _ => congrFun v i⟩))
    rw [ee] at hD
    exact ⟨ask,A,b,fun hf => Bool.noConfusion hf,Nat.cast_le.mp (hk.trans hD)⟩

def sitesAt (t h : ℕ) (ht : 0 < t) (j : Fin h) : Fin (6*t) :=
  ix (6*t) (by omega) (2*j.val)

lemma sitesAt_val {t h : ℕ} (ht : 0 < t) (hh : h ≤ 3*t) (j : Fin h) :
    (sitesAt t h ht j).val = 2*j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)

def pinWord {t h : ℕ} (ht : 0 < t) (u : Fin h → ZMod 2) : Words (6*t) :=
  ∑ j : Fin h, u j • pinVec (sitesAt t h ht j)

lemma pinWord_apply {t h : ℕ} (ht : 0 < t) (hh : h ≤ 3*t) (u : Fin h → ZMod 2)
    (i : Fin (6*t)) :
    pinWord ht u i = if p : i.val % 2=0 ∧ i.val/2<h then u ⟨i.val/2,p.2⟩ else 0 := by
  simp only [pinWord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pinVec, mul_ite, mul_one, mul_zero,
    Fin.ext_iff, sitesAt_val ht hh]
  split_ifs with hp
  · let j : Fin h := ⟨i.val/2,hp.2⟩
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left (show i.val = 2*j.val by dsimp [j]; omega)]
    · intro k _ hne
      apply ite_eq_right
      intro he
      exact hne (Fin.ext (by dsimp [j]; omega))
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    have := j.isLt
    omega

noncomputable def bankParam {t h : ℕ} (ht : 0 < t) (p : C4 × (Fin h → ZMod 2)) : Words (6*t) :=
  bc (6*t) p.1 + pinWord ht p.2

lemma bankParam_apply {t h : ℕ} (ht : 0 < t) (hh : h ≤ 3*t) (p : C4 × (Fin h → ZMod 2))
    (i : Fin (6*t)) :
    bankParam ht p i = fm_beta p.1 (i.val % 6) +
      if v : i.val % 2=0 ∧ i.val/2<h then p.2 ⟨i.val/2,v.2⟩ else 0 := by
  rw [bankParam, Pi.add_apply, fm_bc t (by omega), pinWord_apply ht hh]

lemma bankParam_range {t h : ℕ} (ht : 0 < t) (z : Words (6*t)) :
    z ∈ pinDual (sitesAt t h ht) ↔ ∃ p : C4 × (Fin h → ZMod 2), z = bankParam ht p := by
  rw [pinDual, Submodule.mem_sup]
  constructor
  · rintro ⟨b,hb,u,hu,rfl⟩
    obtain ⟨c,rfl⟩ := (st_mem_Bsp _ b).mp hb
    rw [Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨v,rfl⟩ := hu
    exact ⟨(c,v),rfl⟩
  · rintro ⟨⟨c,v⟩,rfl⟩
    refine ⟨bc _ c,bc_mem _ c,pinWord ht v,?_,rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨v,rfl⟩

lemma beta_determine : ∀ c d : C4, fm_beta c 1 = fm_beta d 1 → fm_beta c 3 = fm_beta d 3 →
    fm_beta c 2 = fm_beta d 2 → fm_beta c 4 = fm_beta d 4 → c = d := by decide

lemma bankParam_injective {t h : ℕ} (ht : 0 < t) (hh : h+2 ≤ 3*t) :
    Function.Injective (bankParam (h := h) ht) := by
  rintro ⟨c,u⟩ ⟨d,v⟩ he
  have hl : h ≤ 3*t := by omega
  have ee (a : ℕ) (ha : a < 6*t) (hh' : ¬ (a%2=0 ∧ a/2<h)) : fm_beta c (a%6) = fm_beta d (a%6) := by
    have w := congrFun he ⟨a,ha⟩
    simp only [bankParam_apply ht hl, hh', ↓reduceDIte, add_zero] at w
    exact w
  have e1 := ee 1 (by omega) (by omega)
  have e3 := ee 3 (by omega) (by omega)
  have e2 := ee (6*t-4) (by omega) (by omega)
  have e4 := ee (6*t-2) (by omega) (by omega)
  rw [show (6*t-4)%6=2 by omega] at e2
  rw [show (6*t-2)%6=4 by omega] at e4
  have ec := beta_determine c d e1 e3 e2 e4
  subst ec
  congr 1
  funext j
  have e := congrFun he (sitesAt t h ht j)
  simpa [bankParam_apply ht hl, sitesAt_val ht hl, j.isLt] using e

lemma bank_trace_sum {t h : ℕ} (ht : 0 < t) (hh : h+2 ≤ 3*t) :
    Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht)) =
      ∑ c : C4, ∑ v : Fin h → ZMod 2, tw (6*t) (by omega) (markT _) (bankParam ht (c,v)) := by
  rw [st_Ssum_image _ _ _ _ _ (bankParam_injective ht hh) (bankParam_range ht), Fintype.sum_prod_type]

def seg (A : ℕ → Mat) (k : ℕ) : Mat := ((List.range k).map A).prod

lemma seg_succ (A : ℕ → Mat) (k : ℕ) : seg A (k+1) = seg A k * A k := List.prod_range_succ _ _

lemma seg_add (A : ℕ → Mat) (k m : ℕ) :
    seg A (k+m) = seg A k * seg (fun i => A (k+i)) m := by
  simp [seg, List.range_add, List.map_map, Function.comp_def]

lemma seg_pair (A : ℕ → Mat) (k : ℕ) :
    seg A (2*k) = seg (fun i => A (2*i) * A (2*i+1)) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [show 2*(k+1) = (2*k+1)+1 by omega, seg_succ, seg_succ, ih, seg_succ, mul_assoc]

lemma seg_step (s : ℕ → ℤ) (m : ℕ) : seg (fun i => step (s i)) m = pathProd s m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [seg_succ, pathProd, ih]

lemma sum_fn_prod (h : ℕ) (f : Fin h → ZMod 2 → Mat) :
    (∑ v : Fin h → ZMod 2, (List.ofFn (fun j => f j (v j))).prod) =
      (List.ofFn (fun j => ∑ x : ZMod 2, f j x)).prod := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (h+1) => ZMod 2)).sum_comp, Fintype.sum_prod_type, List.ofFn_succ]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    simp_rw [← Finset.mul_sum, ih]
    exact (Finset.sum_mul ..).symm

def evenC (c : C4) (j : ℕ) : ZMod 2 := fm_beta c (2*(j%3))
def oddC (c : C4) (j : ℕ) : ZMod 2 := fm_beta c (2*(j%3)+1)

def front (c : C4) (j : ℕ) (v : ZMod 2) : Mat :=
  fm_M (evenC c j + v) * fm_M (oddC c j)

def back (c : C4) (j : ℕ) : Mat := fm_M (evenC c j) * fm_M (oddC c j)

def rowMat (s : ℤ) : Mat := !![1,s;1,s]

def frontSum (c : C4) (j : ℕ) : Mat := (2 : ℤ) • rowMat (sgn (oddC c j))

lemma front_sum (c : C4) (j : ℕ) : ∑ v : ZMod 2, front c j v = frontSum c j := by
  have H : ∀ a b : ZMod 2, fm_M (a+0)*fm_M b + fm_M (a+1)*fm_M b = (2 : ℤ) • rowMat (sgn b) := by
    decide
  exact (Fin.sum_univ_two _).trans (H _ _)

lemma front_prefix (c : C4) (h : ℕ) :
    (∑ v : Fin h → ZMod 2, (List.ofFn (fun j => front c j.val (v j))).prod) = seg (frontSum c) h := by
  rw [sum_fn_prod, seg, ← fm_ofFn h (frontSum c)]
  simp_rw [front_sum]

lemma kill_front3 : ∀ c : C4, c.2.2 ≠ (0,0) → seg (frontSum c) 3 = 0 := by decide

lemma kill_front (c : C4) (h : ℕ) (hh : 3 ≤ h) (hc : c.2.2 ≠ (0,0)) : seg (frontSum c) h = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [seg_add, kill_front3 c hc, zero_mul]

lemma good_odd (a b : ZMod 2) (j : ℕ) : oddC (a,b,0,0) j = 0 := by
  have H : ∀ a b : ZMod 2, ∀ r : Fin 3, fm_beta (a,b,0,0) (2*r.val+1) = 0 := by decide
  exact H a b ⟨j%3,Nat.mod_lt _ (by decide)⟩

lemma good_front (a b : ZMod 2) (h : ℕ) (hp : 0 < h) :
    seg (frontSum (a,b,0,0)) h = (2 : ℤ)^(2*h-1) • rowMat 1 := by
  have he : frontSum (a,b,0,0) = fun _ => (2 : ℤ) • rowMat 1 := by
    funext j
    rw [frontSum, good_odd, sgn_zero]
  rw [he]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  induction k with
  | zero => decide
  | succ k ih =>
    rw [seg_succ, ih (by omega), smul_mul_assoc, mul_smul_comm]
    have H : rowMat 1 * rowMat 1 = (2 : ℤ) • rowMat 1 := by decide
    rw [H, smul_smul, smul_smul, show 2*(k+1+1)-1=(2*(k+1)-1)+2 by omega, pow_add]
    congr 1
    ring

lemma good_back (a b : ZMod 2) (j : ℕ) :
    back (a,b,0,0) j = step (sgn (evenC (a,b,0,0) j)) := by
  rw [back, good_odd]
  exact (show ∀ x : ZMod 2, fm_M x * fm_M 0 = step (sgn x) by decide) _

lemma rowMat_trace (A : Mat) : (rowMat 1 * A).trace = total A := by
  simp [rowMat, total, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

def point {h : ℕ} (c : C4) (v : Fin h → ZMod 2) (i : ℕ) : ZMod 2 :=
  fm_beta c (i%6) + if p : i%2=0 ∧ i/2<h then v ⟨i/2,p.2⟩ else 0

lemma point_even {h : ℕ} (c : C4) (v : Fin h → ZMod 2) (j : ℕ) :
    point c v (2*j) = evenC c j + if p : j<h then v ⟨j,p⟩ else 0 := by
  by_cases hj : j<h <;> simp [point, evenC, show (2*j)%6=2*(j%3) by omega, hj]

lemma point_odd {h : ℕ} (c : C4) (v : Fin h → ZMod 2) (j : ℕ) :
    point c v (2*j+1) = oddC c j := by
  simp [point, oddC, show (2*j+1)%6=2*(j%3)+1 by omega, show (2*j+1)%2=1 by omega]

lemma tw_split {t h m : ℕ} (ht : 0 < t) (hm : h+m=3*t) (c : C4) (v : Fin h → ZMod 2) :
    tw (6*t) (by omega) (markT _) (bankParam ht (c,v)) =
      ((List.ofFn (fun j => front c j.val (v j))).prod * seg (fun i => back c (h+i)) m).trace := by
  rw [fm_tw]
  have he : (fun i : Fin (6*t) => fm_M (bankParam ht (c,v) i)) = fun i => fm_M (point c v i.val) := by
    funext i
    rw [bankParam_apply ht (by omega)]
    rfl
  rw [he, fm_ofFn (6*t) (fun i => fm_M (point c v i))]
  change (seg (fun i => fm_M (point c v i)) (6*t)).trace = _
  rw [show 6*t=2*(h+m) by omega, seg_pair, seg_add]
  congr 2
  · change ((List.range h).map _).prod = _
    rw [← fm_ofFn h (fun j => fm_M (point c v (2*j)) * fm_M (point c v (2*j+1)))]
    congr 2
    funext j
    rw [point_even, point_odd, dite_eq_left j.isLt]
    rfl
  · congr 1
    funext j
    rw [point_even, point_odd, dite_eq_right (by omega), add_zero]
    rfl

lemma avg_tw {t h m : ℕ} (ht : 0 < t) (hm : h+m=3*t) (c : C4) :
    (∑ v : Fin h → ZMod 2, tw (6*t) (by omega) (markT _) (bankParam ht (c,v))) =
      (seg (frontSum c) h * seg (fun i => back c (h+i)) m).trace := by
  simp_rw [tw_split ht hm c]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, front_prefix]

lemma avg_good {t h m : ℕ} (ht : 0 < t) (hm : h+m=3*t) (hp : 0<h) (a b : ZMod 2) :
    (∑ v : Fin h → ZMod 2, tw (6*t) (by omega) (markT _) (bankParam ht ((a,b,0,0),v))) =
      2^(2*h-1)*total (pathProd (fun i => sgn (evenC (a,b,0,0) (h+i))) m) := by
  rw [avg_tw ht hm, good_front a b h hp, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, rowMat_trace]
  simp_rw [good_back]
  rw [seg_step]

lemma sum_good {G : C4 → ℤ} (hz : ∀ c, c.2.2 ≠ (0,0) → G c = 0) :
    ∑ c, G c = G (0,0,0,0) + G (0,1,0,0) + G (1,0,0,0) + G (1,1,0,0) := by
  have h01 (a b : ZMod 2) : G (a,b,0,1) = 0 := hz _ (by change ((0,1) : ZMod 2 × ZMod 2) ≠ _; decide)
  have h10 (a b : ZMod 2) : G (a,b,1,0) = 0 := hz _ (by change ((1,0) : ZMod 2 × ZMod 2) ≠ _; decide)
  have h11 (a b : ZMod 2) : G (a,b,1,1) = 0 := hz _ (by change ((1,1) : ZMod 2 × ZMod 2) ≠ _; decide)
  have two (f : ZMod 2 → ℤ) : ∑ i, f i = f 0+f 1 := Fin.sum_univ_two f
  simp only [Fintype.sum_prod_type, two, h01, h10, h11, add_zero]
  ring

lemma even_phases (j : ℕ) :
    sgn (evenC (0,0,0,0) j) = 1 ∧ sgn (evenC (0,1,0,0) j) = phase 0 j ∧
      sgn (evenC (1,0,0,0) j) = phase 2 j ∧ sgn (evenC (1,1,0,0) j) = phase 1 j := by
  have H : ∀ r : Fin 3, sgn (evenC (0,0,0,0) r.val) = 1 ∧
      sgn (evenC (0,1,0,0) r.val) = phase 0 r.val ∧
      sgn (evenC (1,0,0,0) r.val) = phase 2 r.val ∧
      sgn (evenC (1,1,0,0) r.val) = phase 1 r.val := by decide
  simpa only [evenC, Nat.mod_mod, phase, Nat.add_mod_mod] using H ⟨j%3,Nat.mod_lt _ (by decide)⟩

lemma shift_phase (d h : ℕ) : (fun i => phase d (h+i)) = phase ((d+h)%3) := by
  funext i
  unfold phase
  rw [show (d+(h+i))%3=(((d+h)%3)+i)%3 by omega]

lemma cycle_sum (h : ℕ) (F : ℕ → ℤ) :
    F ((0+h)%3) + F ((2+h)%3) + F ((1+h)%3) = F 0 + F 1 + F 2 := by
  have H : h%3=0 ∨ h%3=1 ∨ h%3=2 := by omega
  rcases H with p | p | p
  · rw [show (0+h)%3=0 by omega, show (1+h)%3=1 by omega, show (2+h)%3=2 by omega]
    ring
  · rw [show (0+h)%3=1 by omega, show (1+h)%3=2 by omega, show (2+h)%3=0 by omega]
    ring
  · rw [show (0+h)%3=2 by omega, show (1+h)%3=0 by omega, show (2+h)%3=1 by omega]
    ring

lemma bank_price {t h : ℕ} (ht : 0<t) (hh : 3≤h) (hs : h+2≤3*t) :
    Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht)) =
      (2 : ℤ)^(2*h-1) * (total (pathProd (fun _ => 1) (3*t-h)) + signedPaths (3*t-h)) := by
  let m := 3*t-h
  have hm : h+m=3*t := by dsimp [m]; omega
  rw [bank_trace_sum ht hs, sum_good (G := fun c =>
    ∑ v : Fin h → ZMod 2, tw (6*t) (by omega) (markT _) (bankParam ht (c,v))) (fun c hc => ?_)]
  · simp_rw [avg_good ht hm (by omega), fun i => (even_phases (h+i)).1,
      fun i => (even_phases (h+i)).2.1, fun i => (even_phases (h+i)).2.2.1,
      fun i => (even_phases (h+i)).2.2.2, shift_phase]
    have H := cycle_sum h (fun d => total (pathProd (phase d) m))
    change _ = _ * (_ + signedPaths m)
    rw [signedPaths, Fin.sum_univ_three]
    rw [show ((0 : Fin 3) : ℕ) = 0 by decide, show ((1 : Fin 3) : ℕ) = 1 by decide,
      show ((2 : Fin 3) : ℕ) = 2 by decide]
    linear_combination (2 : ℤ)^(2*h-1) * H
  · rw [avg_tw ht hm, kill_front c h hh hc, zero_mul, Matrix.trace_zero]

noncomputable def light {n : ℕ} (D : Submodule (ZMod 2) (Words n)) (k : ℕ) :
    Submodule (ZMod 2) (Words n) := Submodule.span (ZMod 2) {z | z ∈ D ∧ wt n z < 4*k+2}

lemma light_le {n : ℕ} (D : Submodule (ZMod 2) (Words n)) (k : ℕ) : light D k ≤ D :=
  Submodule.span_le.mpr (fun _ hz => hz.1)

lemma heavy_of_not_light {n : ℕ} {D : Submodule (ZMod 2) (Words n)} {k : ℕ} {z : Words n}
    (hz : z ∈ D) (hnot : z ∉ light D k) : 4*k+2 ≤ wt n z := by
  by_contra! h
  exact hnot (Submodule.subset_span (show z ∈ {v | v ∈ D ∧ wt n v < 4*k+2} from ⟨hz,h⟩))

lemma wt_even_le {n : ℕ} (w : Words n) : wt n (even n w) ≤ wt n w := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1,fun hz => hi.2 ?_⟩
  rw [even_apply, hz]
  simp

lemma light_even {n k : ℕ} {D : Submodule (ZMod 2) (Words n)}
    (he : ∀ z ∈ D, even n z ∈ D) : ∀ z ∈ light D k, even n z ∈ light D k := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z h =>
    exact Submodule.subset_span ⟨he _ h.1,(wt_even_le z).trans_lt h.2⟩
  | zero => rw [even_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [even_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [even_smul]; exact Submodule.smul_mem _ _ hx

lemma light_support {n : ℕ} (D : Submodule (ZMod 2) (Words n)) (k : ℕ) :
    ∃ S : Finset (Fin n), S.card ≤ Module.finrank (ZMod 2) D * (4*k+1) ∧
      ∀ z ∈ light D k, (Finset.univ.filter (fun i => z i ≠ 0)) ⊆ S := by
  classical
  let supp := fun z : Words n => Finset.univ.filter (fun i => z i ≠ 0)
  obtain ⟨B,hB,hcard,hspan,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2)
    {z : Words n | z ∈ D ∧ wt n z < 4*k+2}
  have hr := Submodule.finrank_mono (light_le D k)
  change B.card = Module.finrank (ZMod 2) (light D k) at hcard
  change Submodule.span (ZMod 2) (B : Set (Words n)) = light D k at hspan
  refine ⟨B.biUnion supp, ?_, ?_⟩
  · calc (B.biUnion supp).card ≤ ∑ z ∈ B, (supp z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ B, (4*k+1) := Finset.sum_le_sum fun z hz => by
        have h : wt n z < 4*k+2 := (hB hz).2
        change wt n z ≤ 4*k+1
        omega
      _ = B.card*(4*k+1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (hcard.le.trans hr)
  · intro z hz i hi
    by_contra hnot
    have hsub : Submodule.span (ZMod 2) (B : Set (Words n)) ≤
        LinearMap.ker (LinearMap.proj i : Words n →ₗ[ZMod 2] ZMod 2) := by
      refine Submodule.span_le.mpr fun w hw => ?_
      change w i = 0
      by_contra hne
      exact hnot (Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩)
    rw [← hspan] at hz
    exact (Finset.mem_filter.mp hi).2 (hsub hz)

lemma light_rank {t h : ℕ} (ht : 0<t) (htall : 100*(h+4)^2 ≤ t)
    (D : Submodule (ZMod 2) (Words (6*t))) (hb : ∀ j, base (6*t) j ∈ D)
    (hd : Module.finrank (ZMod 2) D ≤ h+4) :
    Module.finrank (ZMod 2) (light D (12*(h+4))) ≤ h := by
  let U := light D (12*(h+4))
  let B := Bsp (6*t)
  have hBD : B ≤ D := Submodule.span_le.mpr (fun _ ⟨j,hj⟩ => hj ▸ hb j)
  have hBU : U ⊓ B = ⊥ := by
    obtain ⟨S,hS,hs⟩ := light_support D (12*(h+4))
    have hs' := hS.trans (Nat.mul_le_mul_right _ hd)
    have hsmall : S.card < 2*t := by nlinarith
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    obtain ⟨c,hc⟩ := (st_mem_Bsp _ z).mp hz.2
    by_contra hne
    have hcn : c ≠ 0 := by
      intro eq
      exact hne (hc.trans (eq ▸ cl_bc_zero _))
    have hbig := cl_wt_bc (6*t) t (by omega) rfl c hcn
    rw [← hc] at hbig
    exact (Nat.not_le_of_lt hsmall) (hbig.trans (Finset.card_le_card (hs z hz.1)))
  have hr := Submodule.finrank_sup_add_finrank_inf_eq U B
  rw [hBU, finrank_bot, add_zero] at hr
  have hsup := Submodule.finrank_mono (sup_le (show U ≤ D from light_le D (12*(h+4))) hBD)
  have h4 : 4 ≤ Module.finrank (ZMod 2) B := base_span_finrank _ (by omega) ⟨t,rfl⟩
  change Module.finrank (ZMod 2) U ≤ h
  exact Nat.le_of_add_le_add_right ((Nat.add_le_add_left h4 (Module.finrank (ZMod 2) U)).trans
    (hr.symm.le.trans (hsup.trans hd)))

lemma tail_bound {n k : ℕ} (hn : 0<n) (h6 : 6≤n) (h2 : 2 ∣ n)
    (D U : Submodule (ZMod 2) (Words n)) (hU : U ≤ D)
    (hheavy : ∀ z ∈ D, z ∉ U → 4*k+2 ≤ wt n z) :
    (5 : ℤ)^k * |Ssum n hn (markT n) D - Ssum n hn (markT n) U| ≤
      (Nat.card D : ℤ) * 4^k * ((Iset n hn).card : ℤ) := by
  classical
  let vals := fun V : Submodule (ZMod 2) (Words n) => Finset.univ.filter (fun z => z ∈ V)
  let T := tw n hn (markT n)
  have s (V : Submodule (ZMod 2) (Words n)) : Ssum n hn (markT n) V = ∑ z ∈ vals V, T z := by
    rw [Ssum_eq]
    exact (Finset.sum_filter ..).symm
  have sub : vals U ⊆ vals D := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU (Finset.mem_filter.mp hx).2⟩
  let E := vals D \ vals U
  have er : Ssum n hn (markT n) D - Ssum n hn (markT n) U = ∑ z ∈ E, T z := by
    rw [s,s,sub_eq_iff_eq_add]
    exact (Finset.sum_sdiff sub).symm
  have ec : E.card ≤ Nat.card D := by
    have hc : (vals D).card = Nat.card D := (h6_card_filter (fun z => z ∈ D)).symm
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq hc
  have hz (z) (he : z ∈ E) : 5^k * |T z| ≤ 4^k * ((Iset n hn).card : ℤ) := by
    obtain ⟨hd,hu⟩ := Finset.mem_sdiff.mp he
    exact tw_small n hn h6 h2 z k (hheavy z (Finset.mem_filter.mp hd).2
      (fun hh => hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)))
  rw [er]
  calc (5 : ℤ)^k * |∑ z ∈ E,T z| ≤ 5^k * ∑ z ∈ E, |T z| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ z ∈ E, 5^k*|T z| := Finset.mul_sum ..
    _ ≤ ∑ _z ∈ E, 4^k*((Iset n hn).card : ℤ) := Finset.sum_le_sum hz
    _ = (E.card : ℤ) * (4^k*((Iset n hn).card : ℤ)) := by simp
    _ ≤ (Nat.card D : ℤ) * (4^k*((Iset n hn).card : ℤ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast ec) (by positivity)
    _ = _ := by ring

lemma light_error {n h : ℕ} (hn : 0<n) (h6 : 6≤n) (h2 : 2 ∣ n)
    (D : Submodule (ZMod 2) (Words n)) (hd : Module.finrank (ZMod 2) D ≤ h+4) :
    (4 : ℤ)^(h+4) * |Ssum n hn (markT n) D - Ssum n hn (markT n) (light D (12*(h+4)))| ≤
      ((Iset n hn).card : ℤ) := by
  let H := h+4
  let k := 12*H
  let A := |Ssum n hn (markT n) D - Ssum n hn (markT n) (light D k)|
  let I : ℤ := (Iset n hn).card
  have hI : 0≤I := Nat.cast_nonneg _
  have hx : (5 : ℤ)^k*A ≤ (Nat.card D : ℤ)*4^k*I :=
    tail_bound hn h6 h2 D (light D k) (light_le D k) (fun _ hz hu => heavy_of_not_light hz hu)
  have hcard : (Nat.card D : ℤ) ≤ 2^H := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hd
  have hc : (4 : ℤ)^H*(Nat.card D : ℤ)*4^k ≤ 5^k := by
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity))
      (by positivity : 0 ≤ (4 : ℤ)^k)).trans ?_
    dsimp only [k]
    rw [pow_mul, pow_mul, ← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  change 4^H*A ≤ I
  apply le_of_mul_le_mul_left (a := (5 : ℤ)^k) _ (by positivity)
  calc (5 : ℤ)^k * (4^H*A) = 4^H*(5^k*A) := by ring
    _ ≤ 4^H*((Nat.card D : ℤ)*4^k*I) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = (4^H*(Nat.card D : ℤ)*4^k)*I := by ring
    _ ≤ 5^k*I := mul_le_mul_of_nonneg_right hc hI

lemma adaptive_sparse_bound {t h : ℕ} (ht : 0<t) (htall : 100*(h+4)^2 ≤ t)
    (name c : Words (6*t)) (k : ℕ)
    (hf : feasible (by omega) (sitesAt t h ht) name c false k) :
    ∃ U : Submodule (ZMod 2) (Words (6*t)), (∀ z ∈ U, even (6*t) z ∈ U) ∧
      Module.finrank (ZMod 2) U ≤ h ∧
      (4 : ℤ)^(h+4) * ((k : ℤ)-Ssum (6*t) (by omega) (markT _) U) ≤ (Iset (6*t) (by omega)).card := by
  obtain ⟨D,hb,he,hd,hk⟩ := (adaptive_geometry _ ⟨t,rfl⟩ _ name c k).mp hf
  refine ⟨light D (12*(h+4)),light_even he,light_rank ht htall D hb hd,?_⟩
  have hx := light_error (n := 6*t) (by omega) (by omega) (show 2∣6*t from ⟨3*t,by omega⟩) D hd
  exact (mul_le_mul_of_nonneg_left
    ((sub_le_sub_right hk _).trans (le_abs_self _)) (by positivity)).trans hx

noncomputable def flatSets {n : ℕ} (hn : 0<n) (U : Submodule (ZMod 2) (Words n)) : Finset (Words n) := by
  classical exact (Iset n hn).filter (fun x => x ∈ orth n U.subtype)

noncomputable def pinSets {n : ℕ} (hn : 0<n) (P : Finset (Fin n)) : Finset (Words n) := by
  classical exact (Iset n hn).filter (fun x => ∀ i ∈ P, x i = 0)

lemma flat_score {n : ℕ} (hn : 0<n) (U : Submodule (ZMod 2) (Words n)) :
    Ssum n hn (markT n) U = (2 : ℤ)^Module.finrank (ZMod 2) U * (flatSets hn U).card := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have hu (z : Words n) : z ∈ U ↔ ∃ u : U, z=u.val :=
    ⟨fun h => ⟨⟨z,h⟩,rfl⟩,fun ⟨u,h⟩ => h ▸ u.2⟩
  rw [st_Ssum_image n hn (markT n) U Subtype.val Subtype.val_injective hu]
  simp_rw [kc_tw]
  rw [Finset.sum_comm]
  have hinner (x : Words n) : (∑ u : U,sgn (dot n u.val x)) =
      if x ∈ orth n U.subtype then (Fintype.card U : ℤ) else 0 := by
    rw [← h2_sum_sgn_tau n U.subtype x]
    exact Finset.sum_congr rfl fun u _ => congrArg sgn (dot_comm n u.val x)
  simp_rw [hinner]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  rfl


def price (h m : ℕ) : ℤ :=
  2^(2*h-1)*((Nat.fib (2*m+3) : ℤ) +
    (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^(m/3)).mulVec
      ![if m%3 = 0 then 6 else if m%3 = 1 then 11 else 19,
        if m%3 = 0 then 34 else if m%3 = 1 then 63 else 111]) 0)

lemma closed_price {t h : ℕ} (ht : 0<t) (hh : 3≤h) (hs : h+2≤3*t) :
    Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht)) = price h (3*t-h) :=
  (bank_price ht hh hs).trans (path_price h (3*t-h))

lemma exact_fixed {t h : ℕ} (ht : 0<t) (hh : 3≤h) (hs : h+2≤3*t)
    (name c : Words (6*t)) (k : ℕ) :
    feasible (by omega) (sitesAt t h ht) name c true k ↔ (k : ℤ) ≤ price h (3*t-h) := by
  rw [← closed_price ht hh hs]
  exact fixed_geometry _ ⟨t,rfl⟩ _ name c k

lemma attainable {t h : ℕ} (ht : 0<t) (hh : 3≤h) (hs : h+2≤3*t)
    (name c : Words (6*t)) (fixed : Bool) (k : ℕ) (hk : (k : ℤ) ≤ price h (3*t-h)) :
    feasible (by omega) (sitesAt t h ht) name c fixed k := by
  obtain ⟨ask,A,b,ha,hk'⟩ := (exact_fixed ht hh hs name c k).mpr hk
  exact ⟨ask,A,b,fun _ => ha rfl,hk'⟩

def ExtComparison : Prop :=
  ∀ (t : ℕ) (ht : 0<t) (h : ℕ), 3≤h → h+2≤3*t → 100*(h+4)^2 ≤ t →
    ∀ D : Submodule (ZMod 2) (Words (6*t)), (∀ j, base (6*t) j ∈ D) →
      (∀ z ∈ D, even (6*t) z ∈ D) → Module.finrank (ZMod 2) D ≤ h+4 →
        Ssum (6*t) (by omega) (markT _) D ≤
          Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht))

lemma reduction :
    ExtComparison ↔ ∀ (t : ℕ) (ht : 0<t) (h : ℕ), 3≤h → h+2≤3*t →
      ∀ (name c : Words (6*t)) (fixed : Bool) (k : ℕ), (fixed=true ∨ 100*(h+4)^2≤t) →
        (feasible (by omega) (sitesAt t h ht) name c fixed k ↔ (k : ℤ) ≤ price h (3*t-h)) := by
  constructor
  · intro H t ht h hh hs name c fixed k hfx
    refine ⟨?_,attainable ht hh hs name c fixed k⟩
    cases fixed with
    | true => exact (exact_fixed ht hh hs name c k).mp
    | false =>
      intro hf
      obtain ⟨D,hb,he,hr,hD⟩ := (adaptive_geometry _ ⟨t,rfl⟩ _ name c k).mp hf
      have hlarge : 100*(h+4)^2 ≤ t := hfx.resolve_left (by decide)
      exact hD.trans ((H t ht h hh hs hlarge D hb he hr).trans_eq (closed_price ht hh hs))
  · intro H t ht h hh hs hlarge D hb he hr
    let M := Ssum (6*t) (show 0<6*t by omega) (markT _) D
    have hp : (0 : ℤ) ≤ Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht)) := by
      obtain ⟨A,b,hA⟩ := pinLower (by omega) (show 6 ∣ 6*t from ⟨t,rfl⟩) (sitesAt t h ht) 0 0
      exact (Nat.cast_nonneg _).trans_eq hA
    change M ≤ _
    by_cases hM : 0 ≤ M
    · have hM' : (M.toNat : ℤ) = M := Int.toNat_of_nonneg hM
      have hf : feasible (by omega) (sitesAt t h ht) 0 0 false M.toNat :=
        (adaptive_geometry _ ⟨t,rfl⟩ _ _ _ _).mpr ⟨D,hb,he,hr,hM'.le⟩
      have hu := (H t ht h hh hs 0 0 false M.toNat (Or.inr hlarge)).mp hf
      rw [hM', ← closed_price ht hh hs] at hu
      exact hu
    · exact (le_of_not_ge hM).trans hp

lemma price_classical (h m : ℕ) :
    (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
     let lo : ℤ := if m % 3 = 0 then 6 else if m % 3 = 1 then 11 else 19
     let hi : ℤ := if m % 3 = 0 then 34 else if m % 3 = 1 then 63 else 111
     let correction := (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^(m/3)).mulVec ![lo,hi]) 0
     2^(2*h-1)*((Nat.fib (2*m+3) : ℤ)+correction)) = price h m := by
  unfold price
  convert rfl

def PostedStatement : Prop := (∀ (t : ℕ) (ht : 0 < t) (h : ℕ), 3 ≤ h → h+2 ≤ 3*t →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
    (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let m := 3*t-h
  let lo : ℤ := if m % 3 = 0 then 6 else if m % 3 = 1 then 11 else 19
  let hi : ℤ := if m % 3 = 0 then 34 else if m % 3 = 1 then 63 else 111
  let correction := (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^(m/3)).mulVec ![lo,hi]) 0
  ∀ (name c : W) (fixed : Bool) (k : ℕ), (fixed = true ∨ 100*(h+4)^2 ≤ t) →
    ((∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w = mix w (ix (2*j.val))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔
      (k : ℤ) ≤ 2^(2*h-1)*((Nat.fib (2*m+3) : ℤ)+correction)))

lemma posted_iff_extComparison : PostedStatement ↔ ExtComparison := by
  rw [reduction]
  constructor
  · intro H t ht h hh hs name c fixed k hfx
    have he := H t ht h hh hs name c fixed k hfx
    rw [← price_classical]
    exact he
  · intro H t ht h hh hs
    refine fun name c fixed k hfx => ?_
    have he := H t ht h hh hs name c fixed k hfx
    rw [← price_classical] at he
    exact he

def Block {n : ℕ} (hn : 0<n) (h : ℕ) (U : Submodule (ZMod 2) (Words n)) : Prop :=
  ∃ j : Fin n, ∀ z : Words n, z ∈ U ↔
    ∀ i : Fin n, (¬ ∃ k : Fin h, i=ix n hn (j.val+2*k.val)) → z i=0

lemma rotatedBank {t h : ℕ} (ht : 0<t) (hs : h+2≤3*t) (D U : Submodule (ZMod 2) (Words (6*t)))
    (hU : U ≤ D) (hb : ∀ j, base (6*t) j ∈ D) (hd : Module.finrank (ZMod 2) D ≤ h+4)
    (hblock : Block (by omega) h U) :
    Ssum (6*t) (by omega) (markT _) D = Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht)) := by
  obtain ⟨j,hj⟩ := hblock
  let n := 6*t
  have hn : 0<n := by dsimp [n]; omega
  have h6 : 6 ∣ n := ⟨t,rfl⟩
  let σ := h3_shift n hn j.val j.isLt.le
  have hr (w : Words n) (i : Fin n) : rot n hn j.val w i = w (σ.symm i) := by
    change w (ix n hn (i.val+n-j.val % n)) = w (ix n hn (i.val+n-j.val))
    rw [Nat.mod_eq_of_lt j.isLt]
  have hinj : Function.Injective (rot n hn j.val) := by
    intro a b he
    funext i
    have eq := congrFun he (σ i)
    simpa only [hr,Equiv.symm_apply_apply] using eq
  have hsites (k : Fin h) : σ (sitesAt t h ht k) = ix n hn (j.val+2*k.val) := by
    change ix n hn ((sitesAt t h ht k).val+j.val) = _
    rw [sitesAt_val ht (by omega), add_comm]
  have hu (v : Fin h → ZMod 2) : rot n hn j.val (pinWord ht v) ∈ U := by
    apply (hj _).mpr
    intro i hi
    rw [hr]
    simp only [pinWord,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pinVec]
    apply Finset.sum_eq_zero
    intro k _
    have hne : σ.symm i ≠ sitesAt t h ht k := by
      intro he
      exact hi ⟨k,(σ.apply_symm_apply i).symm.trans ((congrArg σ he).trans (hsites k))⟩
    simp [hne]
  have hBD : Bsp n ≤ D := Submodule.span_le.mpr (fun _ ⟨x,hx⟩ => hx ▸ hb x)
  let α := C4 × (Fin h → ZMod 2)
  let g := fun p : α => rot n hn j.val (bankParam ht p)
  have hg (p : α) : g p ∈ D := by
    change rot n hn j.val (bc n p.1 + pinWord ht p.2) ∈ D
    obtain ⟨c,hc,_⟩ := cl_rot_bc n hn h6 j.val p.1
    rw [cl_rot_add, ← hc]
    exact D.add_mem (hBD (bc_mem _ _)) (hU (hu _))
  let f : α → D := fun p => ⟨g p,hg p⟩
  have gi : Function.Injective g := hinj.comp (bankParam_injective ht hs)
  have fi : Function.Injective f := fun a b he => gi (congrArg Subtype.val he)
  have hcard : Nat.card D ≤ Nat.card α := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D), Nat.card_zmod]
    have ea : Nat.card α = 2^(h+4) := by
      simp [α,C4,pow_add]
      ring
    rw [ea]
    exact Nat.pow_le_pow_right (by decide) hd
  have fs := (fi.bijective_of_nat_card_le hcard).surjective
  have range_g (z : Words n) : z ∈ D ↔ ∃ p : α, z = g p := by
    constructor
    · intro hz
      obtain ⟨p,hp⟩ := fs ⟨z,hz⟩
      exact ⟨p,(congrArg Subtype.val hp).symm⟩
    · rintro ⟨p,rfl⟩
      exact hg p
  rw [st_Ssum_image n hn (markT n) D g gi range_g,
    st_Ssum_image n hn (markT n) _ _ (bankParam_injective ht hs) (bankParam_range ht)]
  exact Finset.sum_congr rfl fun p _ => tw_rot n hn _ _

def ordinary (n h : ℕ) : ℤ := 2^(2*h-1)*(Nat.fib (n-2*h+3) : ℤ)

lemma flatCard {n : ℕ} (hn : 0<n) (U : Submodule (ZMod 2) (Words n)) :
    (flatSets hn U).card = Nat.card {w : Words n //
      (∀ i : Fin n, w i*w (ix n hn (i.val+1)) = 0) ∧ (∀ z ∈ U, (∑ i, w i*z i) = 0)} := by
  classical
  rw [h6_card_filter]
  congr 1
  ext x
  simp only [flatSets,Finset.mem_filter,Finset.mem_univ,true_and,kc_mem_Iset,mem_orth]
  apply and_congr_right
  intro _
  exact ⟨fun h z hz => h ⟨z,hz⟩,fun h z => h z.val z.property⟩

lemma ordinary_stability {n a h : ℕ} (hn : 0<n) (ha : 3≤a) (hn' : n=2*a)
    (hp : 1≤h) (hs : h≤a) (U : Submodule (ZMod 2) (Words n))
    (he : ∀ z ∈ U, even n z ∈ U) (hu : Module.finrank (ZMod 2) U ≤ h) :
    (Block hn h U → Ssum n hn (markT n) U = ordinary n h) ∧
      (¬ Block hn h U → 64*Ssum n hn (markT n) U ≤ 63*ordinary n h) := by
  subst n
  have hg := Stable.cycleStability a (by omega) h ha hp hs U he hu
  rw [flat_score,flatCard]
  constructor
  · intro hb
    unfold ordinary
    exact_mod_cast hg.1 hb
  · intro hb
    unfold ordinary
    exact_mod_cast hg.2 hb

lemma total_independent_bound {t h : ℕ} (ht : 0<t) (hh : 3≤h) (hs : h+2≤3*t) :
    ((Iset (6*t) (by omega)).card : ℤ) ≤ ordinary (6*t) h := by
  let n := 6*t
  have hn : 0<n := by dsimp [n]; omega
  let U : Submodule (ZMod 2) (Words n) := ⊥
  have he : ∀ z ∈ U, even n z ∈ U := by
    intro z hz
    change z=0 at hz
    rw [hz,even_zero]
    exact Submodule.zero_mem _
  have hr : Module.finrank (ZMod 2) U = 0 := finrank_bot _ _
  have ht' : n=2*(3*t) := by dsimp [n]; omega
  have hg := ordinary_stability hn (by omega : 3≤3*t) ht' (by omega : 1≤h) (by omega) U he
    (hr.le.trans (Nat.zero_le _))
  have hflat : flatSets hn U = Iset n hn := by
    ext x
    simp only [flatSets,Finset.mem_filter,and_iff_left_iff_imp]
    intro _
    rw [mem_orth]
    intro u
    have h0 : (u : Words n) = 0 := u.2
    change dot n x u.val = 0
    rw [h0,dot_zero_right]
  have heq : Ssum n hn (markT n) U = ((Iset n hn).card : ℤ) := by
    rw [flat_score,hr,pow_zero,one_mul,hflat]
  by_cases hb : Block hn h U
  · exact (heq.symm.trans (hg.1 hb)).le
  · have g := hg.2 hb
    rw [heq] at g
    change ((Iset n hn).card : ℤ) ≤ ordinary n h
    linarith [Nat.cast_nonneg (α := ℤ) (Iset n hn).card]

lemma signed_nonneg (m : ℕ) : 0 ≤ signedPaths m := by
  have H (d k : ℕ) : ∀ i j : Fin 2, 0 ≤ pathProd (phase d) k i j := by
    induction k with
    | zero =>
      intro i j
      rw [pathProd,Matrix.one_apply]
      split <;> decide
    | succ k ih =>
      intro i j
      rw [pathProd,Matrix.mul_apply]
      apply Finset.sum_nonneg
      intro b _
      refine mul_nonneg (ih i b) ?_
      fin_cases b <;> fin_cases j <;> simp [step,phase] <;> split <;> norm_num
  exact Finset.sum_nonneg (fun d _ => add_nonneg
    (add_nonneg (add_nonneg (H d m 0 0) (H d m 0 1)) (H d m 1 0)) (H d m 1 1))

lemma ordinary_le_price {t h : ℕ} (ht : 0<t) (hh : 3≤h) (hs : h+2≤3*t) :
    ordinary (6*t) h ≤ Ssum (6*t) (by omega) (markT _) (pinDual (sitesAt t h ht)) := by
  rw [bank_price ht hh hs,unsigned_paths]
  unfold ordinary
  rw [show 6*t-2*h+3 = 2*(3*t-h)+3 by omega]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (signed_nonneg _)) (by positivity)

lemma extremal : ExtComparison := by
  intro t ht h hh hs hlarge D hb he hd
  let n := 6*t
  have hn : 0<n := by dsimp [n]; omega
  let U := light D (12*(h+4))
  by_cases block : Block hn h U
  · exact (rotatedBank ht hs D U (light_le D _) hb hd block).le
  · have hU : Module.finrank (ZMod 2) U ≤ h := light_rank ht hlarge D hb hd
    have hEven (z) (hz : z ∈ U) : even n z ∈ U := light_even he z hz
    have hg := (ordinary_stability hn (by omega : 3≤3*t) (by dsimp [n]; omega) (by omega : 1≤h)
      (by omega) U hEven hU).2 block
    have herr := light_error hn (by dsimp [n]; omega) (show 2∣n from ⟨3*t,by dsimp [n]; omega⟩) D hd
    have hc : (64 : ℤ) ≤ 4^(h+4) := calc
      64 = (4 : ℤ)^3 := by decide
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    have he64 : 64*(Ssum n hn (markT n) D - Ssum n hn (markT n) U) ≤ ordinary n h := calc
      _ ≤ 64*|Ssum n hn (markT n) D - Ssum n hn (markT n) U| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ ≤ 4^(h+4)*|Ssum n hn (markT n) D - Ssum n hn (markT n) U| :=
        mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ ≤ ((Iset n hn).card : ℤ) := herr
      _ ≤ ordinary n h := total_independent_bound ht hh hs
    have hu : Ssum n hn (markT n) D ≤ ordinary n h := by linarith only [hg,he64]
    exact hu.trans (ordinary_le_price ht hh hs)

lemma complete : PostedStatement := posted_iff_extComparison.mpr extremal

end PEqualNP.Outside.L_meta_33639_aux

theorem PEqualNP.Outside.L_meta_33639 : (∀ (t : ℕ) (ht : 0 < t) (h : ℕ), 3 ≤ h → h+2 ≤ 3*t →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
    (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let m := 3*t-h
  let lo : ℤ := if m % 3 = 0 then 6 else if m % 3 = 1 then 11 else 19
  let hi : ℤ := if m % 3 = 0 then 34 else if m % 3 = 1 then 63 else 111
  let correction := (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^(m/3)).mulVec ![lo,hi]) 0
  ∀ (name c : W) (fixed : Bool) (k : ℕ), (fixed = true ∨ 100*(h+4)^2 ≤ t) →
    ((∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w = mix w (ix (2*j.val))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔
      (k : ℤ) ≤ 2^(2*h-1)*((Nat.fib (2*m+3) : ℤ)+correction))) := by
  exact PEqualNP.Outside.L_meta_33639_aux.complete
